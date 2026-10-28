import WinnowApp.Common
import Winnow.Wallet.People
import Winnow.Keys.Taproot
import Winnow.Ledger.WalletPolicy
import Winnow.Ledger.Multisig

/-! MultisigViews.swift and MultisigBuildView.swift (upstream 1cf93fb): raw k-of-n multisig accounts in
Advanced mode's Wallet tab only — the Multisig section, MultisigAddView ("Join an account"),
MultisigBuildView ("Create an account"), MultisigAccountView and the collection step (a payment from Send or
a co-signer's pasted PSBT, reviewed against the account's own coins, signed here, combined with the other
signers' copies, finalized and broadcast), and MultisigLiteralRow / MultisigValueRow.

Deliberate departures from upstream (PORT.md, user 2026-10-28): the account page has no payment form of its
own (every payment, the recovery path included, starts from Send), shares its descriptor with one button
instead of printing it, and the create/join wording is plain.

Left out until the Ledger lands, with no stub: "Pair a Ledger (2-of-2)", the builder's "Include a Ledger",
the account's "Verify on Ledger", and "Sign with Ledger". The texts that depend on a paired Ledger (the
signing footer) already follow a record's registration. -/

namespace WinnowApp
open ElmLean

/-! ## Update -/

def Model.multisigInfo? (m : Model) (id : String) : Option MultisigInfo := m.multisig.accounts.find? (·.id == id)

def Model.signer? (m : Model) (id : String) : Option SignerInfo := m.multisig.signers.find? (·.id == id)

def Model.multisigPSBTRoute? (m : Model) : Option String :=
  match m.routes.getLast? with
  | some (.multisigPSBT id) => some id
  | _ => none

/-- MultisigBuildView.blocks(forDays:): about 144 blocks a day; BIP68 counts at most 65,535 blocks. -/
def recoveryBlocks (days : Nat) : Nat := min (days * 144) 0xFFFF

/-- The days a delay of `blocks` comes to, to the nearest day (the stepper's value). -/
def recoveryDays (blocks : Nat) : Nat := max 1 ((blocks + 72) / 144)

/-- `recoveryPlan`. -/
def MultisigBuildForm.recoveryPlan (f : MultisigBuildForm) : Option MultisigRecovery :=
  if !f.withRecovery then none
  else if f.recoveryMode == 0 then some (.fewerSigners f.recoveryThreshold f.recoveryBlocks)
  else some (.separateKey f.recoveryKey.trimAscii.copy f.recoveryBlocks)

/-- `MultisigRecovery` as WalletCore's plan. -/
def MultisigRecovery.plan : MultisigRecovery → Winnow.MultisigAccount.RecoveryPlan
  | .fewerSigners t b => .fewerSigners t b.toUInt32
  | .separateKey key b => .separateKeys 1 #[Winnow.Keys.Unicode.trimWhitespace key] b.toUInt32

def multisigFailureDescription : Winnow.MultisigFailure → String
  | .account e => e.description
  | .named n => s!"The operation could not be completed ({n})."

/-- `MultisigBuildView.previewText`: "2 of 3 members, one of them 2 of 3: 7 ways to spend, each needing every
key it lists, up to 3 keys." -/
def previewText (account : Winnow.MultisigAccount) : String :=
  if !account.isNested then
    s!"{account.policySummary}: any {account.threshold} of the {account.signers.size} keys sign a spend."
  else
    let largest := account.signersLeaves.foldl (fun acc l => max acc l.keys.size) 0
    s!"{account.policySummary}: {account.signersLeaves.size} ways to spend, each needing every key it lists, up to {largest} keys. A member short of the keys it needs cannot help."

/-- `preview`: the account these members make, or why they do not, shown before Create; a recovery key
not pasted yet is left out of it. An account naming a Ledger key must also fit a Ledger's policy. -/
def MultisigBuildForm.computePreview (f : MultisigBuildForm) (network : Network) : Option (Except String String) :=
  if f.members.length < 2 then none else
  let recovery := if f.withRecovery && f.recoveryMode == 1 && f.recoveryKey.isEmpty then none else f.recoveryPlan
  let members := f.members.toArray.map fun m =>
    ({ keys := (m.keys.map (·.key)).toArray, threshold := (m.threshold.getD m.keys.length : Nat) } : Winnow.MultisigAccount.Member)
  let net := match network with | .mainnet => Winnow.Tx.BitcoinNetwork.mainnet | .signet => .signet | .regtest => .regtest
  let made := do
    let d ← Winnow.MultisigAccount.makeNestedDescriptor members f.threshold (recovery.map MultisigRecovery.plan) net
    Winnow.MultisigAccount.make d net
  match made with
  | .error e => some (.error (multisigFailureDescription e))
  | .ok account =>
    if Winnow.Ledger.Multisig.namesALedgerKey account then
      match Winnow.Ledger.WalletPolicy.ofAccount "Preview" account with
      | .ok _ => some (.ok (previewText account))
      | .error e => some (.error e.description)
    else some (.ok (previewText account))

/-- `.onChange(of: members.count)`: both thresholds stay within 1 … members; the preview follows. The
signers' threshold is not lowered below 2 while only this phone is a member: upstream's `onChange` drops
it to 1 when the builder seeds this phone, so every account built without touching the stepper would be
any 1 of its members. -/
def MultisigBuildForm.clamp (f : MultisigBuildForm) (network : Network) : MultisigBuildForm :=
  let n := max f.members.length 1
  let f := { f with threshold := min (max f.threshold 1) (max n 2), recoveryThreshold := min (max f.recoveryThreshold 1) n }
  { f with preview := f.computePreview network }

/-- The threshold the stepper shows: at most the members there are. -/
def MultisigBuildForm.shownThreshold (f : MultisigBuildForm) : Nat := min f.threshold (max f.members.length 1)

def MultisigBuildForm.canCreate (f : MultisigBuildForm) : Bool :=
  !f.creating && (Winnow.DisplayName.normalized f.name).isSome && (f.preview.any fun p => p matches .ok _) &&
    !(f.withRecovery && f.recoveryMode == 1 && f.recoveryKey.isEmpty)

/-- `phoneMember`: this phone as a member of its own. -/
def Model.phoneMember (m : Model) : Option BuildMember :=
  m.multisig.keyExpression.map fun k => { keys := [{ key := k, label := phoneLabel }] }

/-- `add(_:to:)`: a pick joins member `into`, or starts a member of its own. A whole account brings this
phone's key with it, so the key leaves the member it was in. -/
def MultisigBuildForm.addPick (f : MultisigBuildForm) (keys : List BuildKey) (name : Option String) (threshold : Option Nat)
    (into : Option Nat) : MultisigBuildForm :=
  let members := match keys.find? (·.label == phoneLabel) with
    | some phone => (f.members.map fun m => { m with keys := m.keys.filter (·.key != phone.key) }).filter (!·.keys.isEmpty)
    | none => f.members
  let f := { f with members }
  let used := f.usedKeys
  let fresh := keys.filter (!used.contains ·.key)
  if fresh.isEmpty then f else
  match into with
  | some i => if i < f.members.length then { f with members := f.members.modify i fun m => { m with keys := m.keys ++ fresh } } else f
  | none => { f with members := f.members ++ [{ keys := fresh, name, threshold }] }

/-- `removeMember(_:)`: a whole account goes as one; this phone comes back as a member of its own when the
account held its key. -/
def Model.removeBuildMember (m : Model) (i : Nat) : MultisigBuildForm :=
  let f := m.multisigBuild
  let f := { f with members := f.members.eraseIdx i }
  match m.phoneMember with
  | some phone => if f.usedKeys.contains phone.keys[0]!.key then f else { f with members := phone :: f.members }
  | none => f

/-- `remove(_:from:)`: a key out of a member (an empty member goes). -/
def MultisigBuildForm.removeKey (f : MultisigBuildForm) (i k : Nat) : MultisigBuildForm :=
  let members := f.members.modify i fun m => { m with keys := m.keys.eraseIdx k }
  { f with members := members.filter (!·.keys.isEmpty) }

/-- `SignerPickerSheet.accountText`: "2 keys, one signer"; "2 of 3: any 2 of its 3 keys"; why not. -/
def pickerAccountText (a : MultisigInfo) (eligible : Bool) : String :=
  let summary := a.policy.getD "?"
  if !eligible then
    if a.isNested then s!"{summary}: cannot be one member yet" else s!"{summary}: a member of its own only"
  else if a.threshold < a.signerCount then s!"{summary}: any {a.threshold} of its {a.signerCount} keys"
  else s!"{a.signerCount} keys, one signer"

/-- Whether the picker can take the account: not nested, and (joining a member) one whose keys all sign. -/
def pickerAccountEligible (a : MultisigInfo) (wholeMember : Bool) : Bool :=
  a.policy.isSome && !a.isNested && (wholeMember || a.threshold ≥ a.signerCount)

/-- LedgerPairView's Pair button: a usable display name (what this phone calls the Ledger). -/
def LedgerPairForm.nameIsUsable (f : LedgerPairForm) : Bool :=
  (Winnow.DisplayName.normalized f.name).isSome

/-- The descriptor text as MultisigAddView validates it (trimmed; nothing while empty). -/
def MultisigAddForm.trimmed (f : MultisigAddForm) : String := Winnow.Keys.Unicode.trimWhitespace f.descriptor

def MultisigAddForm.validation (f : MultisigAddForm) : Option (Except String MultisigCheck) :=
  match f.check with
  | some (text, r) => if text == f.trimmed then some r else none
  | none => none

def MultisigAddForm.canSave (f : MultisigAddForm) : Bool :=
  !f.saving && (Winnow.DisplayName.normalized f.name).isSome && (f.validation.any fun r => r matches .ok _)

/-- The collection step's state on leaving or backgrounding: an answer in flight no longer counts, and the
paste field empties (every signature is already in the account's draft). -/
def CollectForm.cleared (f : CollectForm) : CollectForm :=
  { f with epoch := f.epoch + 1, busy := false, pasted := "" }

/-- Leave the innermost multisig screen (its state goes with it). -/
def Model.popMultisig (m : Model) : Model :=
  let m' := match m.routes.getLast? with
    | some (.multisigPSBT _) => { m with collect := m.collect.cleared }
    | some .multisigAdd => { m with multisigAdd := {} }
    | some .multisigBuild => { m with multisigBuild := {} }
    | some .ledgerPair => { m with ledgerPair := {} }
    | some (.multisigAccount _) => { m with multisigAccountError := none, collect := { m.collect with error := none } }
    | _ => m
  { m' with routes := m'.routes.dropLast }

/-- Begin an operation of the collection step (`run`): a new epoch, busy, no error. -/
def Model.runCollect (m : Model) : Model × Nat :=
  let e := m.collect.epoch + 1
  ({ m with collect := { m.collect with epoch := e, busy := true, error := none } }, e)

/-- The account whose draft the collection step works on: the Send tab's, the account's collection page,
or the account page itself (its "Paste a PSBT from a co-signer"). -/
def Model.collectingOn? (m : Model) (id : String) : Bool :=
  m.send.collecting == some id || m.multisigPSBTRoute? == some id || m.routes.getLast? == some (.multisigAccount id)

def stepMultisig (msg : MultisigMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  let add := m.multisigAdd
  let build := m.multisigBuild
  let spend := m.collect
  let withAdd (f : MultisigAddForm) : Model := { m with multisigAdd := f }
  let withBuild (f : MultisigBuildForm) : Model := { m with multisigBuild := f }
  let withSpend (f : CollectForm) : Model := { m with collect := f }
  match msg with
  | .openAdd => ({ m with routes := m.routes ++ [.multisigAdd], multisigAdd := {} }, [])
  | .openBuild =>
    -- `seed()`: this phone is the first member; the user adds the rest
    let f : MultisigBuildForm := { members := m.phoneMember.toList }
    ({ m with routes := m.routes ++ [.multisigBuild], multisigBuild := f.clamp m.settings.network }, [])
  | .openAccount id =>
    ({ m with routes := m.routes ++ [.multisigAccount id], multisigAccountError := none, ledgerVerify := {},
              collect := { spend with error := none } },
     [.multisigOverview g])
  | .openPSBT id =>
    ({ m with routes := m.routes ++ [.multisigPSBT id], collect := { epoch := spend.epoch + 1 } }, [])
  | .pop => (m.popMultisig, [])
  -- MultisigAddView
  | .setName s => (withAdd { add with name := s }, [])
  | .setDescriptor s =>
    let f := { add with descriptor := s }
    let text := f.trimmed
    if text.isEmpty then (withAdd { f with check := none }, [])
    else (withAdd f, [.checkMultisigDescriptor g text])
  | .pasteDescriptor => (m, [.paste .multisigDescriptor])
  | .save =>
    if !add.canSave then (m, []) else
    (withAdd { add with saving := true, error := none }, [.addMultisigAccount g m.settings.advancedMode add.name add.descriptor])
  -- MultisigBuildView
  | .buildSetName s => (withBuild { build with name := s }, [])
  | .openPicker into => ({ m with multisigBuild := { build with pickInto := into, pasteError := none } }.present .signerPicker, [])
  | .pickSigner id =>
    match m.signer? id with
    | some s =>
      if s.keys.any build.usedKeys.contains then (m, []) else
      let f := build.addPick (s.keys.map fun k => { key := k, label := s.name }) none none build.pickInto
      { m with multisigBuild := f.clamp m.settings.network }.closeSheet .signerPicker
    | none => (m, [])
  | .pickAccount id =>
    match m.multisigInfo? id with
    | some a =>
      let whole := build.pickInto.isNone
      let phone := m.multisig.keyExpression
      if !pickerAccountEligible a whole || a.signerExpressions.any (fun k => some k != phone && build.usedKeys.contains k) then
        (m, [])
      else
        let keys := a.signerExpressions.map fun k => ({ key := k, label := if some k == phone then phoneLabel else a.name } : BuildKey)
        let threshold := if a.threshold < a.signerCount then some a.threshold else none
        let f := build.addPick keys (some a.name) threshold build.pickInto
        { m with multisigBuild := f.clamp m.settings.network }.closeSheet .signerPicker
    | none => (m, [])
  | .pasteMemberKeys => (m, [.paste .memberKeys])
  | .removeMemberKey i k => (withBuild (build.removeKey i k |>.clamp m.settings.network), [])
  | .removeMember i => ({ m with multisigBuild := (m.removeBuildMember i).clamp m.settings.network }, [])
  | .setThreshold n => (withBuild ({ build with threshold := n }.clamp m.settings.network), [])
  | .setWithRecovery b => (withBuild ({ build with withRecovery := b }.clamp m.settings.network), [])
  | .setRecoveryMode i => (withBuild ({ build with recoveryMode := if i == 1 then 1 else 0 }.clamp m.settings.network), [])
  | .setRecoveryThreshold n => (withBuild ({ build with recoveryThreshold := n }.clamp m.settings.network), [])
  | .pasteRecoveryKey => (m, [.paste .multisigRecoveryKey])
  | .removeRecoveryKey => (withBuild ({ build with recoveryKey := "" }.clamp m.settings.network), [])
  | .setRecoveryDays n =>
    (withBuild ({ build with recoveryBlocks := recoveryBlocks (min (max n 1) 455) }.clamp m.settings.network), [])
  | .create =>
    if !build.canCreate then (m, []) else
    (withBuild { build with creating := true, error := none, registration := none },
     [.createMultisigAccount g m.settings.advancedMode build.name build.threshold (build.members.map (·.plan))
        build.recoveryPlan])
  | .registerLedger id =>
    if m.ledgerRegistering.isSome then (m, []) else
    ({ m with ledgerRegistering := some id, ledgerRegisterError := none }, [.registerLedger g m.settings.advancedMode id])
  -- MultisigAccountView
  | .newAddress =>
    match m.routes.getLast? with
    | some (.multisigAccount id) => ({ m with multisigAccountError := none }, [.newMultisigAddress g id])
    | _ => (m, [])
  | .askRemove =>
    match m.routes.getLast? with
    | some (.multisigAccount id) => ({ m with confirm := some (.removeMultisig id) }, [])
    | _ => (m, [])
  | .remove =>
    match m.confirm with
    | some (.removeMultisig id) => ({ m with confirm := none, multisigAccountError := none }, [.removeMultisigAccount g id])
    | _ => (m, [])
  | .sendFrom id =>
    -- the Send tab with this account under From; a payment being signed and broadcast stays as it is
    let m' := m.switchTab 1
    if m.send.sending then (m', []) else
    let inputs : SendInputs := { network := m.settings.network, accountID := some id }
    ({ m' with send := { inputs } }, [.resolveRate g inputs m.status.feeFloorMilli])
  | .pasteForAccount id =>
    if spend.busy then (m, []) else (withSpend { spend with error := none }, [.paste (.accountPSBT id)])
  -- the collection step
  | .setPasted s => (withSpend { spend with pasted := s }, [])
  | .pastePSBT => (m, [.paste .multisigPSBT])
  | .addPasted id =>
    if spend.busy || spend.pasted.trimAscii.isEmpty then (m, []) else
    let (m', e) := m.runCollect
    (m', [.adoptDraft g e id spend.pasted])
  | .sign id =>
    let ok := ((m.multisigInfo? id).bind (·.draft)).bind (·.screen) |>.any fun s => s.progress.phoneUnsigned && !s.progress.complete
    if spend.busy || !ok then (m, []) else
    let (m', e) := m.runCollect
    (m', [.signDraft g e id])
  | .signWithLedger id =>
    let ok := ((m.multisigInfo? id).bind (·.draft)).bind (·.screen) |>.any fun s => s.progress.ledgerUnsigned && !s.progress.complete
    if spend.busy || !ok then (m, []) else
    let (m', e) := m.runCollect
    (m', [.signDraftWithLedger g e m.settings.advancedMode id])
  | .openLedgerPair => ({ m with routes := m.routes ++ [.ledgerPair], ledgerPair := {} }, [])
  | .setLedgerName s' => ({ m with ledgerPair := { m.ledgerPair with name := s' } }, [])
  | .pairLedger =>
    let f := m.ledgerPair
    if f.pairing || !f.nameIsUsable then (m, []) else
    ({ m with ledgerPair := { f with pairing := true, error := none } }, [.pairLedger g m.settings.advancedMode f.name])
  | .verifyAddress =>
    match m.routes.getLast? with
    | some (.multisigAccount id) =>
      match m.multisigInfo? id with
      | some a =>
        if m.ledgerVerify.checking then (m, []) else
        ({ m with ledgerVerify := { id, index := a.nextReceiveIndex, checking := true } },
         [.verifyLedgerAddress g m.settings.advancedMode id a.nextReceiveIndex])
      | none => (m, [])
    | _ => (m, [])
  | .broadcast id =>
    let ok := ((m.multisigInfo? id).bind (·.draft)).bind (·.screen) |>.any (·.progress.complete)
    if spend.busy || !ok then (m, []) else
    if m.spendingInFlight then
      (withSpend { spend with error := some "Another payment is already being signed and broadcast. Wait for it to finish." }, [])
    else
      let (m', e) := m.runCollect
      ({ m' with spendingInFlight := true }, [.broadcastDraft g e id])
  | .askDiscard id => ({ m with confirm := some (.discardDraft id) }, [])
  | .discard =>
    match m.confirm with
    | some (.discardDraft id) =>
      let (m', e) := { m with confirm := none }.runCollect
      (m', [.discardDraft g e id])
    | _ => (m, [])
  | .rebroadcast id txid => ({ m with payment := { m.payment with error := none } }, [.rebroadcastSpend g id txid])
  | .askAbandon id txid => ({ m with confirm := some (.abandonSpend id txid) }, [])
  | .abandon =>
    match m.confirm with
    | some (.abandonSpend id txid) => ({ m with confirm := none }, [.abandonSpend g id txid])
    | _ => (m, [])

/-- The backend's multisig answers (`onHost` hands them here). -/
def Model.onMultisigHost (m : Model) (h : Host) : Model × List Cmd :=
  let current (g : Nat) := g == m.generation
  let spend := m.collect
  -- an answer for the collection step counts only while it shows that account and the operation's epoch lasts
  let accepts (g e : Nat) (id : String) := current g && e == spend.epoch && m.collectingOn? id && m.active
  match h with
  | .multisig g o =>
    -- the draft's review comes with the overview (re-reviewed whenever the draft, coins or tip move)
    if !current g then (m, []) else ({ m with multisig := o }, [])
  | .multisigChecked g text r =>
    if current g && m.multisigAdd.trimmed == text then ({ m with multisigAdd := { m.multisigAdd with check := some (text, r) } }, [])
    else (m, [])
  | .multisigAdded g _ registration =>
    if !current g then (m, []) else
    let m' := { m with multisigAdd := { m.multisigAdd with saving := false } }
    match registration with
    | some (.error reason) =>
      -- saved, but the paired Ledger did not register it: the screen stays, with Done
      let text := s!"The account is on this phone, but the Ledger did not register it: {reason} Register on Ledger from the account screen."
      ({ m' with multisigAdd := { m'.multisigAdd with saved := true, error := some text } }, [.multisigOverview g])
    | _ =>
      -- `dismiss()`
      (if m'.routes.getLast? == some .multisigAdd then m'.popMultisig else m', [.multisigOverview g])
  | .multisigCreated g id d registration =>
    if !current g then (m, []) else
    ({ m with multisigBuild := { m.multisigBuild with creating := false, created := some (id, d), registration } },
     [.multisigOverview g])
  | .ledgerRegistered g id r =>
    if !current g then (m, []) else
    let m' := { m with ledgerRegistering := none }
    match r with
    | .ok () =>
      let b := m'.multisigBuild
      let b := if b.created.any (·.1 == id) then
          { b with registration := some (.ok ((b.pairedLedgerNames m.multisig.ledgers).head?.getD "the Ledger")) } else b
      ({ m' with multisigBuild := b, ledgerRegisterError := none }, [.multisigOverview g])
    | .error e => ({ m' with ledgerRegisterError := some (id, e) }, [.multisigOverview g])
  | .multisigRemoved g id =>
    if !current g then (m, []) else
    (if m.routes.getLast? == some (.multisigAccount id) then m.popMultisig else m, [.multisigOverview g])
  | .drafted g id =>
    if !current g then ({ m with spendingInFlight := false }, []) else
    -- "Sign and continue" filed the draft: the Send tab goes on to collect its signatures
    ({ m with send := { m.send with sending := false, collecting := some id, error := none }, spendingInFlight := false,
              collect := { epoch := spend.epoch + 1 } },
     [.multisigOverview g, .refresh g])
  | .collected g e id fromPaste =>
    if !accepts g e id then (m, [.multisigOverview m.generation]) else
    let m' := { m with collect := { spend with busy := false, pasted := if fromPaste then "" else spend.pasted } }
    -- the account page's paste filed the draft: its collection step opens
    let m' := if m.routes.getLast? == some (.multisigAccount id) then { m' with routes := m'.routes ++ [.multisigPSBT id] } else m'
    (m', [.multisigOverview g, .refresh g])
  | .spendHandled g _ _ => if current g then (m, [.multisigOverview g, .refresh g]) else (m, [])
  | .ledgerPaired g _ =>
    if !current g then (m, []) else
    let m' := { m with ledgerPair := { m.ledgerPair with pairing := false } }
    -- `dismiss()`
    (if m'.routes.getLast? == some .ledgerPair then m'.popMultisig else m', [.multisigOverview g])
  | .ledgerAddressShown g id index r =>
    if !current g || m.ledgerVerify.id != id || m.ledgerVerify.index != index then (m, []) else
    let result := match r with
      | .ok _ => ("The Ledger derived this same address. Compare it with the one on its screen.", false)
      | .error e => (e, true)
    ({ m with ledgerVerify := { m.ledgerVerify with checking := false, result := some result } }, [])
  | .draftBroadcast g e id txid =>
    let m := { m with spendingInFlight := false }
    if !accepts g e id then (m, [.refresh m.generation, .multisigOverview m.generation]) else
    if m.send.collecting == some id then
      -- the Send tab's receipt, with the main path's relay watch
      ({ m with send := { m.send with sentTxid := some txid, collecting := none }, collect := { spend with busy := false } },
       [.multisigOverview g, .refresh g, .rawTransaction g txid, .watchRelay g txid])
    else
      ({ m with collect := { spend with busy := false, broadcastTxid := some txid } },
       [.multisigOverview g, .refresh g, .watchRelay g txid])
  | _ => (m, [])

/-! ## View -/

/-- MultisigLiteralRow: a literal (an address, a key expression) with a copy button (below it: beside a
literal this long the renderer's row leaves the button no room). -/
def literalRow (m : Model) (key text : String) (id := "") : H :=
  .col [withId id (literal text), .button (if m.copied == some key then "Copied" else "Copy") .plain (some (.copy key text))]

/-- The Wallet tab's multisig section. -/
def multisigSection (m : Model) : H :=
  .section "Multisig" "Accounts that need more than one signature to spend. Pair a Ledger or save other people's keys in Settings → Signers."
    ((match m.multisig.notice with | some n => [body n] | none => []) ++
     (m.multisig.accounts.map fun a =>
        .row [.identified s!"multisigAccount-{a.id}" (navLink a.name (some (.multisig (.openAccount a.id))) (symbol := "person.3")), .spacer,
              Html.tone .secondary (body (satsText a.balance))]) ++
     [ .col [.identified "multisigBuildButton" (navLink "Create an account" (some (.multisig .openBuild)) (symbol := "plus.circle")),
             caption "You choose who signs, then share the account with them."]
     , .col [.identified "multisigAddButton" (navLink "Join an account" (some (.multisig .openAdd)) (symbol := "person.badge.plus")),
             caption "Paste the account someone shared with you."] ])

def errorSection (e : Option String) : List H :=
  match e with
  | some text => [.section "" "" [body text]]
  | none => []

/-- `LedgerRegisterButton`: registers the account on the Ledger connected now. -/
def ledgerRegisterRows (m : Model) (id : String) : List H :=
  let busy := m.ledgerRegistering == some id
  [.identified "ledgerRegisterButton"
    (.button (if busy then "Check the Ledger's screen…" else "Register on Ledger") .plain
      (if m.ledgerRegistering.isSome then none else some (.multisig (.registerLedger id))))] ++
  (match m.ledgerRegisterError with
   | some (i, e) => if i == id then [.identified "ledgerRegisterError" (body e)] else []
   | none => [])

/-- MultisigAddView ("Join an account"). -/
def multisigAddSections (m : Model) : List H :=
  let f := m.multisigAdd
  let set (g : String → MultisigMsg) : String → Msg := fun s => .multisig (g s)
  [ .section "" ""
      [.identified "multisigNameField" (.input .plain "" "Name" f.name (set .setName) none)]
  , .section "This phone's key" "Send this to whoever is creating the account."
      (match m.multisig.keyExpression with
       | some key =>
         [ literalRow m "multisig.key" key "multisigKeyText" ] ++
         -- `MemberShareRows`: this phone's key with each paired Ledger's, as one signer
         (if m.multisig.ledgers.isEmpty then []
          else m.multisig.ledgers.map fun l =>
            .col [caption s!"Or this phone with {l.name}, as one signer",
                  literalRow m s!"multisig.share.{l.id}" (key ++ "\n" ++ l.keys.headD "") s!"multisigMemberShareCopy-{l.id}"])
       | none => [caption "This wallet has no shareable account key."])
  , .section "Account" "Winnow finds coins sent to it from now on."
      ([ .identified "multisigDescriptorField" (.input .multiline "" "Paste the account (tr(…))" f.descriptor (set .setDescriptor) none)
       , .identified "multisigDescriptorPasteButton" (.button "Paste" .plain (some (.multisig .pasteDescriptor))) ] ++
       (match f.validation with
        | some (.ok c) =>
          [.identified "multisigAddPolicy" (.labeled "Policy" c.policy)] ++
          (match c.firstAddress with
           | some a => [.col [caption "First address", .identified "multisigFirstAddress" (caption a)]]
           | none => []) ++
          (match c.ledgerName with
           | some l => [.identified "multisigJoinLedgerNotice" (caption s!"{l} holds a key of this account and approves it on its screen after Save.")]
           | none => [])
        | some (.error e) => [body e]
        | none => [])) ] ++
  errorSection f.error

def multisigAddScreen (m : Model) (inner : List H) : H :=
  let f := m.multisigAdd
  .screen "Join an account" (some (.multisig .pop))
    ([ .toolbar [.identified "multisigSaveButton"
                   (if f.saved then .button "Done" .primary (some (.multisig .pop))
                    else .button (if f.saving then "Saving…" else "Save") .primary (if f.canSave then some (.multisig .save) else none))]
     , .list (multisigAddSections m) ] ++ inner)

/-- `MemberRow`: one member, its keys by fingerprint and name, ⊕ to add a key that signs with it (or −
to take a whole account out), − on each key but this phone's. -/
def memberRow (m : Model) (member : BuildMember) (i : Nat) : H :=
  let network := m.settings.network
  let fingerprint (k : String) : String :=
    match Winnow.MultisigAccount.signerKey k (match network with | .mainnet => .mainnet | .signet => .signet | .regtest => .regtest) with
    | .ok single => (single.origin.map (Winnow.Wallet.hex8 ·.fingerprint)).getD "?"
    | .error _ => "?"
  .identified s!"multisigBuildMember-{i}"
    (.col ([.row [.text member.title .title, .spacer,
                  if member.isThreshold then
                    .identified s!"multisigBuildMemberRemove-{i}" (.button "Remove this member" .destructive (some (.multisig (.removeMember i))))
                  else
                    .identified s!"multisigBuildMemberAddKey-{i}" (.button "⊕ Add a key" .plain (some (.multisig (.openPicker (some i)))))]] ++
           (member.keys.zipIdx.map fun (k, ki) =>
              .row ([caption s!"{fingerprint k.key}  {k.label}", .spacer] ++
                    (if k.label != phoneLabel && !member.isThreshold then
                      [.button "−" .destructive (some (.multisig (.removeMemberKey i ki)))] else []))) ++
           (match member.caption with | some c => [caption c] | none => [])))

/-- MultisigBuildView ("Create an account"). -/
def multisigBuildSections (m : Model) : List H :=
  let f := m.multisigBuild
  let n := f.members.length
  let ledgers := f.pairedLedgerNames m.multisig.ledgers
  match f.created with
  | some (id, descriptor) =>
    let info := m.multisigInfo? id
    [.section "" "Send this account to every other signer; each should see the same first address."
      ([ .identified "multisigBuildCreated" (.text "Account created" .title) ] ++
       (match f.registration with
        | some (.ok ledger) => [.identified "multisigBuildLedgerRegistered" (caption s!"Approved on {ledger}.")]
        | some (.error reason) =>
          [.identified "multisigBuildLedgerError" (body s!"The account is on this phone, but the Ledger did not register it: {reason}")] ++
          (if info.any (·.needsLedgerRegistration) then ledgerRegisterRows m id else [])
        | none => []) ++
       [ .qr descriptor, copyableBlock m "multisig.created" descriptor "multisigCreatedDescriptor"
       , .identified "multisigOpenAccountButton" (.button "Open the account" .plain (some (.multisig (.openAccount id)))) ])]
  | none =>
    [ .section "" "A Ledger shows the name when it registers the account: plain letters, digits and punctuation."
        [.identified "multisigBuildNameField" (.input .plain "" "Name" f.name (fun s => .multisig (.buildSetName s)) none)]
    , .section s!"Members · {n}" "Each member is one signer: this phone, a Ledger, someone's keys, or an account here. A member with several keys needs them all."
        ((f.members.zipIdx.map fun (member, i) => memberRow m member i) ++
         [.identified "multisigBuildAddMemberButton" (.button "Add a member" .plain (some (.multisig (.openPicker none))))])
    , .section "" ""
        ([.identified "multisigBuildThresholdStepper"
          (.stepper s!"Any {f.shownThreshold} of {n} members spend" f.shownThreshold 1 (max n 1) (fun k => .multisig (.setThreshold k)) " ")] ++
         [match f.preview with
          | some (.ok text) => .identified "multisigBuildPolicyPreview" (caption text)
          | some (.error e) => .identified "multisigBuildPolicyPreview" (body e)
          | none => caption "Add at least one more member."])
    , .section "" (if f.withRecovery then "Once a coin has sat unmoved this long, the recovery path can spend it without the other signers." else "")
        ([.identified "multisigBuildRecoveryToggle" (.toggle "Recovery after a delay" f.withRecovery (fun b => .multisig (.setWithRecovery b)))] ++
         (if !f.withRecovery then [] else
           [.identified "multisigRecoveryModePicker"
             (.picker "After the delay" ["Fewer signers", "A recovery key"] f.recoveryMode (fun i => .multisig (.setRecoveryMode i)))] ++
           (if f.recoveryMode == 0 then
             [.identified "multisigBuildRecoveryThresholdStepper"
               (.stepper s!"Any {f.recoveryThreshold} of the {n} members" f.recoveryThreshold 1 (max n 1)
                  (fun k => .multisig (.setRecoveryThreshold k)) " ")]
            else if f.recoveryKey.isEmpty then
             [.identified "multisigBuildPasteRecoveryKeyButton" (.button "Paste the recovery key" .plain (some (.multisig .pasteRecoveryKey)))]
            else
             [caption f.recoveryKey, .button "Remove the recovery key" .destructive (some (.multisig .removeRecoveryKey))]) ++
           [.identified "multisigBuildRecoveryDaysStepper"
             (.stepper s!"After about {recoveryDays f.recoveryBlocks} days ({groupDigits f.recoveryBlocks} blocks)"
                (recoveryDays f.recoveryBlocks) 1 455 (fun k => .multisig (.setRecoveryDays k)) " ")]))
    , .section ""
        (if ledgers.isEmpty then "Winnow watches the account from the next block it scans."
         else s!"Then approve the account in the Bitcoin app on {" and ".intercalate ledgers} (Bitcoin Test on signet; 2.2.1 or later for a recovery path or a nested account).")
        [.identified "multisigBuildCreateButton"
          (.button (if f.creating then "Creating…" else "Create account") .primary (if f.canCreate then some (.multisig .create) else none))] ] ++
    (match f.error with
     | some e => [.section "" "" [.identified "multisigBuildError" (body e)]]
     | none => [])

/-- MultisigAccountView. -/
def multisigAccountSections (m : Model) (id : String) : List H :=
  match m.multisigInfo? id with
  | some a =>
    match a.policy with
    | some policy =>
      [ .section "" ""
          ([.identified "multisigBalance" (.labeled "Balance" (satsText a.balance)),
            .identified "multisigPolicy" (.labeled "Policy" policy)] ++
           (match a.recovery with | some r => [.identified "multisigRecovery" (.labeled "Recovery" r)] | none => []) ++
           (match a.ledgerName with
            | some l => [.identified "multisigLedgerFingerprint" (.labeled "Ledger" l)]
            | none => if a.needsLedgerRegistration then ledgerRegisterRows m a.id else []))] ++
      (match a.membersHeader with
       | some header =>
         [.section header ""
           (a.memberLines.zipIdx.map fun (line, i) => .identified s!"multisigMember-{i}" (caption line))]
       | none => []) ++
      [ .section s!"Receive · index {a.nextReceiveIndex}" "The same address on every signer's device: check it there before sharing it."
          ((match a.receiveAddress with
            | some address => [.qr address, literalRow m "multisig.receive" address "multisigReceiveAddress"]
            | none => []) ++
           (if a.ledgerFingerprint.isNone then [] else
             let v := m.ledgerVerify
             let mine := v.id == a.id && v.index == a.nextReceiveIndex
             [.identified "ledgerVerifyButton"
               (.button (if mine && v.checking then "Check the Ledger's screen…" else "Verify on Ledger") .plain
                  (if mine && v.checking then none else some (.multisig .verifyAddress)))] ++
             (match v.result with
              | some (text, _) => if mine then [.identified "ledgerVerifyResult" (caption text)] else []
              | none => [])) ++
           [.identified "multisigNewAddressButton" (.button "New address" .plain (some (.multisig .newAddress)))])
      -- every payment starts from Send (the recovery path too); a co-signer's PSBT is pasted, never typed
      , .section "" ""
          (if a.draft.isSome then
            [.identified "multisigDraftButton" (.button "Payment awaiting signatures" .plain (some (.multisig (.openPSBT a.id))))]
           else
            [ .identified "multisigSendButton" (.button "Send from this account" .plain (some (.multisig (.sendFrom a.id))))
            , .identified "multisigPastePSBTButton"
                (.button (if m.collect.busy then "Reading the PSBT…" else "Paste a PSBT from a co-signer") .plain
                  (if m.collect.busy then none else some (.multisig (.pasteForAccount a.id)))) ] ++
            (match m.collect.error with
             | some e => if m.collect.busy then [] else [.identified "multisigPasteError" (body e)]
             | none => []))
      , .section "Coins" ""
          ((if a.coins.isEmpty then [caption "No coins yet."] else []) ++
           a.coins.map fun c =>
             .col ([body (satsText c.amount), caption c.line] ++
                   (match c.recoveryFrom with | some h => [caption s!"recovery path from block {h}"] | none => [])))
      , .section "" "Everyone who signs needs this to see the account."
          [.identified "multisigShareButton" (.share "Share with co-signers" a.descriptor)]
      , .section "" "" [.button "Remove account" .destructive (some (.multisig .askRemove))] ] ++
      errorSection m.multisigAccountError
    | none => [.section "" "" [caption "This multisig account is no longer on this phone."]] ++ errorSection m.multisigAccountError
  | none => [.section "" "" [caption "This multisig account is no longer on this phone."]] ++ errorSection m.multisigAccountError

/-- `MultisigSigningSections`: the signature-collection step for an account's draft, shared by Send
(after "Sign and continue"), Transactions' draft row and the account's PSBT page: the review of the draft,
the signature counts on every leaf that can finish it, this phone's and the Ledger's signatures, a pasted
co-signer's copy, the PSBT to share (BIP174 v0), Finalize and broadcast, and Discard. Every change goes
through the account's draft, so leaving the screen loses nothing. -/
def collectSections (m : Model) (id : String) : List H :=
  let f := m.collect
  let set (g : String → MultisigMsg) : String → Msg := fun s => .multisig (g s)
  match (m.multisigInfo? id).bind (·.draft) with
  | none => [.section "" "" [caption "This account has no payment awaiting signatures."]] ++ errorSection f.error
  | some d =>
    let review : H :=
      .section "Check this payment" "Check the addresses, amounts and fee on every signer's device before signing."
        (match d.screen with
         | some s =>
           (s.outputs.map fun o =>
              .col [.row [caption (if o.owned then "Back to this account" else "Pays"), .spacer, body (satsText o.amount)],
                    caption o.address]) ++
           [.labeled "Inputs" (satsText s.inputTotal), .identified "multisigFee" (.labeled "Fee" (satsText s.fee))] ++
           (s.signatures.zipIdx.map fun ((recovery, approved, threshold), i) =>
              let (title, rowID) := s.signatureTitles[i]?.getD
                (if recovery then ("Recovery signatures", "multisigRecoverySignatureCount") else ("Signatures", "multisigSignatureCount"))
              .identified rowID (.labeled title s!"{approved} of {threshold}"))
         | none =>
           [ .row [.icon "exclamationmark.triangle.fill", body "Winnow cannot safely review this PSBT"]
           , body (d.reviewError.getD "The account or PSBT is unavailable.") ])
    let actions : List H := match d.screen with
      | some s =>
        let p := s.progress
        [.section (if s.recoveryUsable then "Signing · signers or recovery path" else "Signing") p.nextStep
          ([ .identified "multisigSignButton" (.button "Add this phone's signature" .plain
              (if f.busy || !p.phoneUnsigned || p.complete then none else some (.multisig (.sign id)))) ] ++
           (if p.ledgerHolds then
             [.identified "ledgerSignButton"
               (.button "Sign with Ledger" .plain (if f.busy || !p.ledgerUnsigned || p.complete then none else some (.multisig (.signWithLedger id))))]
            else []) ++
           [ .identified "multisigBroadcastButton" (.button (if f.busy then "Working…" else "Finalize and broadcast") .primary
               (if f.busy || !p.complete then none else some (.multisig (.broadcast id)))) ])]
      | none => []
    let paste : H :=
      .section "Another signer's PSBT" "A pasted copy of this payment is combined with the signatures here."
        [ .identified "psbtPasteField" (.input .multiline "" "Paste a PSBT (Base64)" f.pasted (set .setPasted) none)
        , .identified "psbtPasteButton" (.button "Paste from clipboard" .plain (some (.multisig .pastePSBT)))
        , .identified "addPSBTButton" (.button "Combine" .plain
            (if f.busy || f.pasted.trimAscii.isEmpty then none else some (.multisig (.addPasted id)))) ]
    [review] ++ actions ++ [paste] ++
    (match f.error with
     | some e => [.section "" "" [.identified "multisigError" (body e)]]
     | none => []) ++
    [ .section "PSBT to share" "" [copyableBlock m "multisig.psbt" d.psbt "multisigPSBTText"]
    , .section "" "" [.identified "multisigDiscardDraftButton"
        (.button "Discard draft" .destructive (if f.busy then none else some (.multisig (.askDiscard id))))] ]

/-- The account's collection page (Transactions' draft row, the account page's "Payment awaiting
signatures" and its pasted PSBT): the collection step, then the receipt. It has no payment form of its own:
payments start from Send. -/
def multisigPSBTSections (m : Model) (id : String) : List H :=
  match m.collect.broadcastTxid with
  | some txid => [.section "" "" [.identified "multisigPaymentSent" (.text "Payment sent" .title),
                                  literalRow m "multisig.txid" txid "multisigTxid"]]
  | none => collectSections m id

def multisigPSBTTitle (m : Model) (id : String) : String :=
  if ((m.multisigInfo? id).bind (·.draft)).isSome && m.collect.broadcastTxid.isNone then "Awaiting signatures" else "Payment"

end WinnowApp
