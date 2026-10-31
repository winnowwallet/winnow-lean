import Winnow.IO.Gateways

/-! # The routed HTTP client (`Network/Transport/RoutedHTTPClient.swift`): policy in Lean, fetch injected

Lean has no TLS API (PORT.md, "Known fragility"), so the actual fetch is an injected `HttpFetch`: on
iOS the shell's `http.get` capability (URLSession, ephemeral), in tests `curlFetch`. What stays here is
the client's policy, which is what the Swift code decides:

* `permits`: http or https, a non-empty host, no credentials in the URL, a port in 1…65535.
* Redirects: followed only to a permitted URL on the same host (case-insensitive) and never from
  https to http. A refused redirect is **not** an error of its own: URLSession then returns the 3xx
  response itself, which fails the `200` check as `HTTPFailure(statusCode: 3xx)` — so Swift's
  `Failure.redirect` is never thrown, and neither is it here.
* The response must be `200`; a declared `Content-Length` above the cap, or a body past it, is
  `tooLarge` (exactly `maximumBytes` bytes is accepted).
* After `cancel` every request is refused with `unavailable`.
* The routing gate (`RoutedHTTPClient(proxy:enabled:)`, `init(gateways:)`): a disabled client refuses
  every request with `unavailable` before any fetch; a client with a SOCKS proxy (the Tor gateway when
  clearnet is off) names it on every hop (`HttpRequest.socks`, resolved by the proxy) with URLSession's
  longer 90 s / 180 s limits; a proxy that is not a plausible gateway disables the client.

`HttpFetch` performs one hop and does not follow redirects (a capability that follows them itself under
the same rule simply never returns `redirect`). At most 16 hops are followed. Not covered: in-flight
cancellation of a running fetch (Swift cancels the URLSession task), and progress callbacks fire once
per 64 KiB of the returned body rather than while it streams. -/

namespace Winnow.IO
open Winnow.Net (PeerEndpoint)

structure HttpRequest where
  url : String
  accept : Option String := none
  /-- The fetch may stop reading after `maximumBytes + 1` body bytes. -/
  maximumBytes : Nat
  /-- URLSession `timeoutIntervalForRequest` (inactivity) and `timeoutIntervalForResource`. -/
  requestTimeoutSeconds : Nat := 30
  resourceTimeoutSeconds : Nat := 120
  /-- A SOCKS5 proxy to fetch through, the host named to it unresolved (`--socks5-hostname`). -/
  socks : Option PeerEndpoint := none
  deriving Repr, Inhabited

inductive HttpHop where
  /-- A final response: status, the declared `Content-Length` if any, and the body read so far. -/
  | response (status : Nat) (expectedLength : Option Nat) (body : ByteArray)
  /-- A 3xx with a `Location` (not followed by the fetch). -/
  | redirect (status : Nat) (location : String)
  deriving Inhabited

abbrev HttpFetch := HttpRequest → NetM HttpHop

/-! ## URLs -/

/-- The parts of a URL the policy reads (`URL.scheme`, `.host`, `.user`, `.password`, `.port`). -/
structure ParsedURL where
  scheme : String
  user : Option String := none
  password : Option String := none
  host : String
  port : Option Nat := none
  /-- Path, query and fragment, as written. -/
  rest : String := ""
  deriving Repr, Inhabited, BEq

private def isSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- A small RFC 3986 parser for absolute `scheme://authority…` URLs (`none` where `URL(string:)` would
fail or give a URL without an authority). -/
def parseURL (s : String) : Option ParsedURL := do
  let cs := s.toList
  if cs.any (fun c => c == ' ' || c.toNat < 0x21 || c.toNat == 0x7F) then none
  let colon ← cs.findIdx? (· == ':')
  let scheme := String.ofList (cs.take colon)
  if scheme.isEmpty || !(scheme.front.isAlpha) || !scheme.all isSchemeChar then none
  let after := cs.drop (colon + 1)
  if !(after.take 2 == ['/', '/']) then none
  let rest := after.drop 2
  let authEnd := (rest.findIdx? (fun c => c == '/' || c == '?' || c == '#')).getD rest.length
  let authority := rest.take authEnd
  let tail := String.ofList (rest.drop authEnd)
  let (userinfo, hostport) := match authority.findIdx? (· == '@') with
    | some _ =>
      let atPos := authority.length - 1 - ((authority.reverse.findIdx? (· == '@')).getD 0)
      (some (authority.take atPos), authority.drop (atPos + 1))
    | none => (none, authority)
  let (user, password) := match userinfo with
    | none => (none, none)
    | some ui => match ui.findIdx? (· == ':') with
      | some i => (some (String.ofList (ui.take i)), some (String.ofList (ui.drop (i + 1))))
      | none => (some (String.ofList ui), none)
  let (host, portText) ←
    if hostport.head? == some '[' then
      let close ← hostport.findIdx? (· == ']')
      let h := String.ofList ((hostport.take close).drop 1)
      let after := hostport.drop (close + 1)
      match after with
      | [] => some (h, none)
      | ':' :: p => some (h, some p)
      | _ => none
    else match hostport.findIdx? (· == ':') with
      | some i => some (String.ofList (hostport.take i), some (hostport.drop (i + 1)))
      | none => some (String.ofList hostport, none)
  let port ← match portText with
    | none => some none
    | some [] => some none
    | some p => if p.all Char.isDigit then some (some (String.ofList p).toNat!) else none
  return { scheme, user, password, host, port, rest := tail }

def ParsedURL.render (u : ParsedURL) : String :=
  let host := if u.host.contains ':' then s!"[{u.host}]" else u.host
  let ui := match u.user, u.password with
    | some us, some pw => s!"{us}:{pw}@" | some us, none => s!"{us}@" | none, _ => ""
  let port := match u.port with | some p => s!":{p}" | none => ""
  s!"{u.scheme}://{ui}{host}{port}{u.rest}"

/-- `RoutedHTTPClient.permits`. -/
def permitsURL (u : ParsedURL) : Bool :=
  let scheme := u.scheme.toLower
  (scheme == "http" || scheme == "https") && !u.host.isEmpty && u.user.isNone && u.password.isNone &&
    (let port := u.port.getD (if scheme == "https" then 443 else 80); port > 0 && port ≤ 65535)

def permits (url : String) : Bool := (parseURL url).map permitsURL |>.getD false

/-- A `Location` resolved against the URL that answered with it (absolute, `//authority`, `/path`,
or a path relative to the current directory). -/
def resolveLocation (base : ParsedURL) (location : String) : Option ParsedURL :=
  if let some u := parseURL location then some u
  else if location.startsWith "//" then parseURL (base.scheme ++ ":" ++ location)
  else
    let root := { base with rest := "" }.render
    if location.startsWith "/" then parseURL (root ++ location)
    else
      let path := (base.rest.splitOn "?")[0]!
      let pcs := path.toList
      let dir := match pcs.reverse.findIdx? (· == '/') with
        | some i => String.ofList (pcs.take (pcs.length - i))
        | none => "/"
      parseURL (root ++ dir ++ location)

/-- The `RedirectPolicy` delegate: whether to follow `from` → `to`. -/
def followsRedirect (source target : ParsedURL) : Bool :=
  permitsURL target && !(source.scheme == "https" && target.scheme != "https") &&
    target.host.toLower == source.host.toLower

/-! ## The client -/

structure RoutedHTTPClient where
  fetch : HttpFetch
  closed : IO.Ref Bool
  /-- The SOCKS5 gateway every request goes through (none: direct). -/
  proxy : Option PeerEndpoint := none
  /-- False when routing allows no HTTP at all (I2P alone, or an invalid proxy): every request is refused. -/
  enabled : Bool := true

namespace RoutedHTTPClient

def maxHops : Nat := 16

/-- `RoutedHTTPClient(proxy:enabled:)`: a proxy that is not a plausible gateway disables the client. -/
def new (fetch : HttpFetch) (proxy : Option PeerEndpoint := none) (enabled : Bool := true) : IO RoutedHTTPClient := do
  return { fetch, closed := ← IO.mkRef false, proxy,
           enabled := enabled && (proxy.isNone || PeerGatewayConfiguration.validProxy proxy) }

/-- `RoutedHTTPClient(gateways:)`: direct with clearnet, through the Tor gateway without it, and no HTTP
at all on I2P alone (its outproxy is never asked for a public host). -/
def ofGateways (fetch : HttpFetch) (g : PeerGatewayConfiguration) : IO RoutedHTTPClient :=
  new fetch (proxy := g.httpProxy) (enabled := g.permitsHTTP)

def isCancelled (c : RoutedHTTPClient) : BaseIO Bool := c.closed.get
/-- Once cancelled a client refuses every later request. -/
def cancel (c : RoutedHTTPClient) : BaseIO Unit := c.closed.set true

def get (c : RoutedHTTPClient) (url : String) (maximumBytes : Nat) (accept : Option String := none)
    (progress : Option (Nat → IO Unit) := none) : NetM ByteArray := do
  let some start := parseURL url | throw (.http .unavailable)
  if !c.enabled || !permitsURL start || maximumBytes == 0 then throw (.http .unavailable)
  if ← c.closed.get then throw (.http .unavailable)
  let (requestTimeoutSeconds, resourceTimeoutSeconds) := if c.proxy.isSome then (90, 180) else (30, 120)
  let mut current := start
  for _ in [0:maxHops] do
    match ← c.fetch { url := current.render, accept, maximumBytes, requestTimeoutSeconds, resourceTimeoutSeconds,
                      socks := c.proxy } with
    | .redirect status location =>
      match resolveLocation current location with
      | some target => if followsRedirect current target then current := target; continue
                       else throw (.http (.status status))
      | none => throw (.http (.status status))
    | .response status expected body =>
      if status != 200 then throw (.http (.status status))
      if let some n := expected then if n > maximumBytes then throw (.http .tooLarge)
      if body.size > maximumBytes then throw (.http .tooLarge)
      if ← c.closed.get then throw (.http .cancelled)
      if let some p := progress then
        let mut n := 65_536
        while n ≤ body.size do p n; n := n + 65_536
        p body.size
      return body
  throw (.http (.transport "too many redirects"))

end RoutedHTTPClient

/-! ## A `curl` fetch, for tests (the iOS shell supplies its own) -/

private def headerValue (lines : List String) (name : String) : Option String :=
  lines.findSome? fun l =>
    match l.splitOn ":" with
    | k :: vs => if k.trimAscii.toString.toLower == name then some (":".intercalate vs).trimAscii.toString else none
    | [] => none

/-- For tests on macOS only (iOS has no `curl`; the shell's `http.get` capability is the fetch there).
One hop with `curl`: no redirects followed, no cookies, no cache, http/https only, URLSession's
timeouts (`--speed-time` for the inactivity limit), the body read up to `maximumBytes + 1`. -/
def curlFetch (curl : String := "curl") : HttpFetch := fun req => do
  let (hh, hpath) ← IO.FS.createTempFile
  hh.flush
  let args := #["-sS", "--proto", "=http,https", "--max-redirs", "0", "--no-keepalive",
    "--connect-timeout", toString req.requestTimeoutSeconds, "--speed-limit", "1", "--speed-time",
    toString req.requestTimeoutSeconds, "--max-time", toString req.resourceTimeoutSeconds,
    "-D", hpath.toString, "-o", "-"] ++ (match req.accept with | some a => #["-H", s!"Accept: {a}"] | none => #[]) ++
    (match req.socks with
     | some p => #["--socks5-hostname", if p.host.contains ':' then s!"[{p.host}]:{p.port}" else s!"{p.host}:{p.port}"]
     | none => #[]) ++
    #["--", req.url]
  let child ← IO.Process.spawn { cmd := curl, args, stdout := .piped, stderr := .piped, stdin := .null }
  let mut body := ByteArray.empty
  let mut truncated := false
  repeat
    let chunk ← child.stdout.read 65_536
    if chunk.isEmpty then break
    body := body ++ chunk
    if body.size > req.maximumBytes then
      truncated := true
      child.kill
      break
  let err ← child.stderr.readToEnd
  let code ← child.wait
  let headerText ← IO.FS.readFile hpath
  try IO.FS.removeFile hpath catch _ => pure ()
  -- The last response block in the dump (a 100-continue may precede it).
  let blocks := (headerText.splitOn "\r\n\r\n").filter (!·.trimAscii.isEmpty)
  let lines := ((blocks.getLast?.getD "").splitOn "\r\n")
  let status := match lines.head? with
    | some l => match l.splitOn " " with
      | _ :: s :: _ => s.toNat?
      | _ => none
    | none => none
  match status with
  | none =>
    if truncated then throw (.http .tooLarge)
    throw (.http (.transport s!"curl exited {code}: {err.trimAscii}"))
  | some st =>
    if 300 ≤ st && st < 400 then
      if let some loc := headerValue lines.tail "location" then return .redirect st loc
    if !truncated && code != 0 then throw (.http (.transport s!"curl exited {code}: {err.trimAscii}"))
    let expected := (headerValue lines.tail "content-length").bind String.toNat?
    return .response st expected body

end Winnow.IO
