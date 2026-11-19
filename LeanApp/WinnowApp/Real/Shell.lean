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
  raw bytes. With `userPresence` the wallet secret's item is behind the person's presence: the Keychain
  itself gives it only under the authentication the app has just asked for (`keychainContext`), and a read
  with none is refused (`errSecInteractionNotAllowed`), never a prompt. An item an earlier build stored
  without it is given it in place when the wallet opens (`upgradeProtection`). The sealed stores' keys (kept
  as text through `store`, under `store-key.`) and a restore's search key (raw bytes) are read at launch and
  in sync passes with nobody there, and stay `WhenUnlockedThisDeviceOnly` alone. 0.9.17 to 0.9.21 gave the
  stores' keys the access control too; `RecordsReal.repairRefusedStoreKeys` takes it off them.
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

/-- The authentication the person has just given, kept by the shell for the Keychain reads of the one action
it was asked for (`auth` with `keep`; `withKeychainContext`): its id while that action runs, none otherwise.
A read of the wallet's secret names it. One at a time is enough: an action is started by the person, and a
second one's authentication replaces the first's here without ending it early in the shell. -/
initialize keychainContext : IO.Ref (Option String) ← IO.mkRef none

/-- Runs `act` under the kept authentication `context`, and ends it when `act` is over, however it ends: the
shell forgets it (`auth.end`), so nothing later in the process reads the secret on the strength of it. With
no context (test mode, or a shell that kept none) `act` runs as it is. -/
def withKeychainContext (ask : Ask) (context : Option String) (act : IO α) : IO α := do
  let some id := context | act
  keychainContext.set (some id)
  try act
  finally
    keychainContext.modify fun held => if held == some id then none else held
    try discard <| ask "auth.end" (Json.mkObj [("context", Json.str id)]) catch _ => pure ()

/-- The ids of the sealed stores' keys (`RecordsReal.accountPrefix`): kept as text through `store`, and read in
sync passes and at launch with nobody there, so never behind the person's presence. -/
def storeKeyPrefix : String := "store-key."

open LeanNative.Native in
/-- The Keychain capability as a `KeyStore`, under `service` (test mode passes its own namespace).
`userPresence` puts the wallet's secret behind the person's presence (the module documentation), and that
secret alone: a sealed store's key, which goes through `store` too, is read at every launch and in sync passes
with nobody there. 0.9.17 to 0.9.21 put every item `store` added behind it, those keys included
(`RecordsReal.repairRefusedStoreKeys` takes them back out). -/
def shellKeyStore (ask : Ask) (service : String := walletService) (userPresence : Bool := false) : KeyStore IO :=
  let item (id : String) : Client.Keychain.Item := { key := id, service := some service }
  let guarded (id : String) : Client.Keychain.Item :=
    { item id with access := if userPresence && !id.startsWith storeKeyPrefix then .userPresence else .unlocked }
  let call {α} (r : Client.Request α) : ExceptT KeyStoreError IO α := do
    match ← (callAsk ask r : IO _) with
    | .ok a => pure a
    | .error e => throw (keychainError e)
  { store := fun secret id => do
      let some _ := String.fromUTF8? secret.serialized | throw .malformedSecret
      match ← call (Client.Keychain.add (guarded id) secret.serialized) with
      | .added => pure ()
      | .alreadyExists => throw (.alreadyExists id)
    load := fun id => do
      let context ← (keychainContext.get : IO _)
      match ← (callAsk ask (Client.Keychain.getText (item id) context) : IO _) with
      | .ok (some text) =>
        match WalletSecret.parse text.toUTF8 with
        | .ok s => pure s
        | .error e => throw e
      | .ok none => throw (.notFound id)
      -- raw bytes, not text: not a wallet secret this store reads (loadBytes sees it)
      | .error e => if e.name == "notText" then throw (.notFound id) else throw (keychainError e)
    delete := fun id => call (Client.Keychain.delete (item id))
    -- in place and attributes only: the shell's one `SecItemUpdate`, which never deletes, adds or reads the
    -- value. A wallet that only watches has no item to protect
    upgradeProtection := fun id => do
      unless userPresence do return false
      match ← (callAsk ask (Client.Keychain.protect (item id)) : IO _) with
      | .ok changed => pure changed
      | .error e => if e.code == some (-25300) then pure false else throw (keychainError e)
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
