import Lean.Data.Json
import Winnow.IO.Http
import Winnow.Keys.KeyStore
import LeanNative.Native.Client.Keychain
import LeanNative.Native.Client.Http

/-! # The iOS shell's capabilities as the WalletCore interfaces

Through LeanNative's typed clients (`LeanNative.Native.Client.Keychain`, `Client.Http`), which build the
shell's `keychain.*` and `http.get` requests and read their answers. `ask name args` is the app's
`Effects.ask`, which may be called from any thread.

* `KeyStore IO` (KeychainStore.swift's contract): the wallet secret's account is the wallet ID under
  the service `org.btc-swift.wallet` (the shell's `service` argument). `store` refuses an occupied ID
  (`alreadyExists`) with the shell's atomic `keychain.add`, never a read then a write; a missing item is
  `notFound`, an unreadable one `malformedSecret`, and any other Keychain failure its `OSStatus`
  (`errSecInteractionNotAllowed` while locked is not "no wallet"). An item that is not UTF-8 text (the
  Swift app's raw store keys) reads as `notFound`; `loadBytes` / `storeBytes` see and keep such items as
  raw bytes. The shell's item is `WhenUnlockedThisDeviceOnly`; it does not add Winnow's user-presence
  flag (the app asks for device authentication before every read instead).
* `HttpFetch`: one request, with its `Accept` header. The shell follows same-host redirects itself
  (never https → http); the declared length is not reported (the body size is checked here). -/

namespace WinnowApp.Real
open Lean Winnow Winnow.IO Winnow.Keys

def walletService : String := "org.btc-swift.wallet"

abbrev Ask := String → Json → IO (Task Json)

open LeanNative.Native in
/-- A typed request through `ask` (the clients' `Request.call` over an `Effects`, from `Effects.ask` alone). -/
def callAsk (ask : Ask) (r : Client.Request α) : IO (Client.Result α) := do
  return r.read (← IO.wait (← ask r.capability r.args))

open LeanNative.Native in
/-- A Keychain failure as the store's error: its `OSStatus`, or `errSecParam` for an answer the shell
should not have given (the client keeps it whole; the store's errors have no room for it). -/
def keychainError (e : Client.Error) : KeyStoreError :=
  .keychain (Int32.ofInt (e.code.getD (-50)))

open LeanNative.Native in
/-- The Keychain capability as a `KeyStore`, under `service` (test mode passes its own namespace). -/
def shellKeyStore (ask : Ask) (service : String := walletService) : KeyStore IO :=
  let item (id : String) : Client.Keychain.Item := { key := id, service := some service }
  let call {α} (r : Client.Request α) : ExceptT KeyStoreError IO α := do
    match ← (callAsk ask r : IO _) with
    | .ok a => pure a
    | .error e => throw (keychainError e)
  { store := fun secret id => do
      let some _ := String.fromUTF8? secret.serialized | throw .malformedSecret
      match ← call (Client.Keychain.add (item id) secret.serialized) with
      | .added => pure ()
      | .alreadyExists => throw (.alreadyExists id)
    load := fun id => do
      match ← (callAsk ask (Client.Keychain.getText (item id)) : IO _) with
      | .ok (some text) =>
        match WalletSecret.parse text.toUTF8 with
        | .ok s => pure s
        | .error e => throw e
      | .ok none => throw (.notFound id)
      -- raw bytes, not text: not a wallet secret this store reads (loadBytes sees it)
      | .error e => if e.name == "notText" then throw (.notFound id) else throw (keychainError e)
    delete := fun id => call (Client.Keychain.delete (item id))
    loadBytes := fun id => call (Client.Keychain.get (item id))
    storeBytes := fun bytes id => do
      match ← call (Client.Keychain.add (item id) bytes) with
      | .added => pure ()
      | .alreadyExists => throw (.alreadyExists id) }

open LeanNative.Native in
/-- The `http.get` capability as the routed client's fetch; a SOCKS gateway goes as `socks` (the shell
answers `bad-proxy` to a malformed one). -/
def shellFetch (ask : Ask) : HttpFetch := fun req => do
  let request : Client.Http.Request :=
    { url := req.url, maxBytes := req.maximumBytes, timeout := some req.requestTimeoutSeconds, accept := req.accept
      socks := req.socks.map (fun p => (p.host, p.port.toNat)) }
  let r ← (callAsk ask (Client.Http.get request) : IO _)
  match r with
  | .ok resp => return .response resp.status none resp.body
  | .error e =>
    match e.kind, e.name with
    | _, "tooLarge" => throw (.http .tooLarge)
    | _, "response" => throw (.http .response)
    | _, "bad-proxy" => throw (.http .unavailable)
    | .malformed, _ => throw (.http .response)
    -- a system error is its text, as the shell gave it; any other name as it came
    | _, "system" => throw (.http (.transport e.detail))
    | _, name => throw (.http (.transport name))

end WinnowApp.Real
