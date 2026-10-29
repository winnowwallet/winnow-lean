import Lean.Data.Json
import Winnow.IO.Http
import Winnow.Keys.KeyStore

/-! # The iOS shell's capabilities as the WalletCore interfaces

ElmLean's native shell (its capabilities, framework/lean/ElmShell/Capabilities.lean) offers `keychain.get/set/delete`
(`key`, `value`; answers `{"value":…|null}` / `{"ok":…}`) and `http.get` (`url`, `maxBytes`,
`timeout`; answers `{"status":…,"body":hex}` or `{"error":…}`). `ask name args` is the app's
`Effects.ask`, which may be called from any thread.

* `KeyStore IO` (KeychainStore.swift's contract): the wallet secret's account is the wallet ID under
  the service `org.btc-swift.wallet` (the shell's `service` argument). `store` refuses an occupied ID
  (`alreadyExists`), a missing item is `notFound`, an unreadable one `malformedSecret`. An item that is
  not UTF-8 text (the Swift app's raw store keys) answers no `value`, so it reads as `notFound`;
  `loadBytes` / `storeBytes` see and keep such items as raw bytes (`hex`). The shell's
  item is `WhenUnlockedThisDeviceOnly`; it does not add Winnow's user-presence flag (the app asks for
  device authentication before every read instead).
* `HttpFetch`: one request, with its `Accept` header. The shell follows same-host redirects itself
  (never https → http); the declared length is not reported (the body size is checked here). -/

namespace WinnowApp.Real
open Lean Winnow Winnow.IO Winnow.Keys

def walletService : String := "org.btc-swift.wallet"

abbrev Ask := String → Json → IO (Task Json)

private def askNow (ask : Ask) (name : String) (args : Json) : IO Json := do
  IO.wait (← ask name args)

private def keyArgs (service id : String) : List (String × Json) :=
  [("key", Json.str id), ("service", Json.str service)]

/-- The `OSStatus` a failed `keychain.set` / `keychain.delete` answered (`errSecParam` if none). -/
private def status (r : Json) : Int32 := Int32.ofInt ((r.getObjValAs? Int "status").toOption.getD (-50))

/-- The Keychain capability as a `KeyStore`, under `service` (test mode passes its own namespace). -/
def shellKeyStore (ask : Ask) (service : String := walletService) : KeyStore IO where
  store secret id := do
    let existing ← (askNow ask "keychain.get" (Json.mkObj (keyArgs service id)) : IO Json)
    if let .ok (.str _) := existing.getObjVal? "value" then throw (.alreadyExists id)
    let some text := String.fromUTF8? secret.serialized | throw .malformedSecret
    let r ← (askNow ask "keychain.set" (Json.mkObj (keyArgs service id ++ [("value", Json.str text)])) : IO Json)
    unless (r.getObjValAs? Bool "ok").toOption.getD false do throw (.keychain (status r))
  load id := do
    let r ← (askNow ask "keychain.get" (Json.mkObj (keyArgs service id)) : IO Json)
    match r.getObjVal? "value" with
    | .ok (.str text) =>
      match WalletSecret.parse text.toUTF8 with
      | .ok s => pure s
      | .error e => throw e
    | _ => throw (.notFound id)
  delete id := do
    let r ← (askNow ask "keychain.delete" (Json.mkObj (keyArgs service id)) : IO Json)
    unless (r.getObjValAs? Bool "ok").toOption.getD false do throw (.keychain (status r))
  loadBytes id := do
    let r ← (askNow ask "keychain.get" (Json.mkObj (keyArgs service id ++ [("hex", Json.bool true)])) : IO Json)
    match r.getObjVal? "hex" with
    | .ok (.str h) => match ofHex? h with | some b => pure (some b) | none => throw .malformedSecret
    | _ => pure none
  storeBytes bytes id := do
    let existing ← (askNow ask "keychain.get" (Json.mkObj (keyArgs service id ++ [("hex", Json.bool true)])) : IO Json)
    if let .ok (.str _) := existing.getObjVal? "hex" then throw (.alreadyExists id)
    let r ← (askNow ask "keychain.set" (Json.mkObj (keyArgs service id ++ [("hex", Json.str (hex bytes))])) : IO Json)
    unless (r.getObjValAs? Bool "ok").toOption.getD false do throw (.keychain (status r))

/-- The `http.get` capability as the routed client's fetch; a SOCKS gateway goes as
`"socks": {"host", "port"}` (the shell answers `{"error":"bad-proxy"}` to a malformed one). -/
def shellFetch (ask : Ask) : HttpFetch := fun req => do
  let args := Json.mkObj [("url", Json.str req.url), ("maxBytes", toJson req.maximumBytes),
                          ("timeout", toJson req.requestTimeoutSeconds)] |>.setObjVal! "accept"
                (match req.accept with | some a => Json.str a | none => Json.null)
  let args := match req.socks with
    | some p => args.setObjVal! "socks" (Json.mkObj [("host", Json.str p.host), ("port", toJson p.port.toNat)])
    | none => args
  let r ← (askNow ask "http.get" args : IO Json)
  match r.getObjValAs? Nat "status", r.getObjValAs? String "body" with
  | .ok status, .ok body =>
    match ofHex? body with
    | some bytes => return .response status none bytes
    | none => throw (.http .response)
  | _, _ =>
    match r.getObjValAs? String "error" with
    | .ok "tooLarge" => throw (.http .tooLarge)
    | .ok "response" => throw (.http .response)
    | .ok "bad-proxy" => throw (.http .unavailable)
    | .ok e => throw (.http (.transport e))
    | .error _ => throw (.http .response)

end WinnowApp.Real
