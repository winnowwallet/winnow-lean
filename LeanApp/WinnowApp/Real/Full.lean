import WinnowApp.Real.Assemble
import WinnowApp.Real.RecordsBackend
import WinnowApp.Real.Multisig

/-! # `Backend.real`: the core half with the records half plugged in

The records (`people.json`, `receive-labels.json` of the network directory) open where AppModel's
`configurePeople` runs: on every `Hooks.configure` (boot, adopting a wallet, deleting one). The core
reaches them through the other `Hooks`; the records fields of `Backend` reach the core through
`RecordsCtx`. (The vault store and the vault send path went with vaults, upstream 1cf93fb.) -/

namespace WinnowApp
open Winnow Winnow.IO

namespace Real
open RecordsReal

/-- The records of the open network directory. -/
structure RecordsHost where
  keys : StoreKeyVault
  current : IO.Ref (Option RecordsStore)
  /-- `e2e?.journal(_:fields:)`, handed to every store opened here. -/
  journal : String → List (String × String) → IO Unit := fun _ _ => pure ()

namespace RecordsHost

def new (keyStore : Keys.KeyStore IO) (journal : String → List (String × String) → IO Unit := fun _ _ => pure ()) :
    IO RecordsHost := do
  return { keys := StoreKeyVault.ofKeyStore keyStore, current := ← IO.mkRef none, journal }

/-- The open records; before the first `configure` there are none (`noWallet`). -/
def store (h : RecordsHost) : IO RecordsStore := do
  match ← h.current.get with
  | some s => return s
  | none => failWith .noWallet

/-- `configurePeople` for `dir`: re-read when the directory is the open one. Damage to people is a
notice, never `storageDamaged`, so this answers `none`. -/
def configure (h : RecordsHost) (n : WinnowApp.Network) (dir : String) : IO (Option String) := do
  match ← h.current.get with
  | some s =>
    if s.network == Network.tx n && s.dir == some (System.FilePath.mk dir) then s.configure
    else openAt
  | none => openAt
  return none
where
  openAt : IO Unit := do
    let s ← RecordsStore.open (Network.tx n) (some (System.FilePath.mk dir)) h.keys
    h.current.set (some { s with journal := h.journal })

def withStore {α} (h : RecordsHost) (none' : α) (f : RecordsStore → IO α) : IO α := do
  match ← h.current.get with
  | some s => f s
  | none => return none'

/-- `nextPaymentAddress(for:)` of a saved person, with the review's recipient. -/
def personPayment (h : RecordsHost) (personID : String) : IO (String × UInt32 × PreviewRecipient) := do
  let s ← h.store
  let some p := (← s.read).people.record? personID | RM.toIO (throw (.people .unknownPerson))
  let (address, index) ← RM.toIO (nextPaymentAddress s personID)
  return (address, index, { personID := p.id, name := p.name, derivesFreshAddresses := p.derivesFreshAddresses,
                            hasUnverifiedFundingDestination := p.hasUnverifiedFundingDestination })

def hooks (h : RecordsHost) : Hooks where
  configure := h.configure
  personPayment := h.personPayment
  advancePersonIndex := fun id index => h.withStore () fun s => discard <| advancePersonPaymentIndex s none id index

end RecordsHost

def RecordsHost.ctx (h : RecordsHost) (env : Env) : RecordsCtx :=
  { store := h.store, wallet := env.currentWallet, http := env.httpGet, journal := env.deps.journal }

end Real

/-- The multisig fields of `Backend` over the core and the account store (`Real/Multisig.lean`). -/
def Real.MultisigApp.install (a : Real.MultisigApp) (env : Real.Env) (base : Backend) : Backend :=
  { base with
    multisigOverview := Real.overview env a
    checkMultisigDescriptor := Real.checkMultisigDescriptor env a
    addMultisigAccount := fun adv name d => do
      let r ← Real.addMultisigAccount env a name d
      return (r.id, ← Real.registerAfterSaving env a adv r)
    removeMultisigAccount := Real.removeMultisigAccount a
    newMultisigReceiveAddress := Real.newMultisigReceiveAddress a
    createMultisigAccount := fun adv name k members rec => do
      let r ← Real.createMultisigAccount env a adv name k members rec
      return (r.id, r.descriptor, ← Real.registerAfterSaving env a adv r)
    registerLedger := fun adv id => discard <| Real.registerLedger env a adv id
    pairLedger := fun adv name => do return (← Real.pairLedger env a adv name).id
    addSignerKeys := fun adv name text => do return (← Real.addSignerKeys env a adv name text).id
    renameSigner := Real.renameSigner a
    removeSigner := Real.removeSigner a
    verifyLedgerAddress := Real.verifyLedgerAddress env a
    -- a payment from an account goes through the account's review; the wallet's otherwise
    previewSend := fun inputs => if inputs.accountID.isSome then Real.previewAccountSend env a inputs else base.previewSend inputs
    signAndDraft := fun adv inputs p => Real.signAndDraft env a adv inputs p
    signDraft := Real.signDraft env a
    signDraftWithLedger := Real.signDraftWithLedger env a
    adoptDraft := Real.adoptDraft env a
    broadcastDraft := Real.broadcastDraft env a
    discardDraft := Real.discardDraft env a
    createDraft := Real.createDraft env a
    rebroadcastSpend := Real.rebroadcastSpend env a
    abandonSpend := Real.abandonSpend env a }

/-- The real backend over the injected capabilities, with its diagnostics handle and the multisig store:
the core half (`Real/Assemble.lean`), the records half (`Real/Records*.lean`) and the multisig accounts
(`Real/Multisig*.lean`) joined through `Hooks`. -/
def Backend.realWithMultisig (deps : Real.Deps) (ledger : IO Real.LedgerSession := Real.noLedger) :
    IO (Backend × Real.Env × Real.MultisigApp) := do
  let host ← Real.RecordsHost.new deps.keyStore deps.journal
  let multisig ← Real.MultisigApp.new (RecordsReal.StoreKeyVault.ofKeyStore deps.keyStore) ledger
  let env ← Real.Env.new { deps with hooks := multisig.allHooks host.hooks }
  multisig.env.set (some env)
  let ctx := host.ctx env
  let base := multisig.install env (ctx.install env.backend)
  return ({ base with records := host.withStore {} fun _ => ctx.records }, env, multisig)

/-- The real backend with its diagnostics handle. -/
def Backend.realWithEnv (deps : Real.Deps) (ledger : IO Real.LedgerSession := Real.noLedger) :
    IO (Backend × Real.Env) := do
  let (b, env, _) ← Backend.realWithMultisig deps ledger
  return (b, env)

/-- The real backend: the Lean WalletCore, the network stack and the records behind every field. -/
def Backend.real (deps : Real.Deps) (ledger : IO Real.LedgerSession := Real.noLedger) : IO Backend := do
  return (← Backend.realWithEnv deps ledger).1

end WinnowApp
