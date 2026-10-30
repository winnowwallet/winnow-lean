import WinnowApp.Multisig

/-! SignerViews.swift (upstream d2ca878): Settings → Signers (Advanced mode only): this phone's key, the
Ledgers it paired and the keys other people sent, which Wallet → Multisig builds accounts from; one
signer's detail (rename, keys, remove); LedgerPairView (moved here from the Multisig section: it files
the Ledger's key and registers nothing); SignerKeysAddView ("Save keys someone sent"). -/

namespace WinnowApp
open ElmLean

/-! ## Update -/

/-- The keys of SignerKeysAddView's text (`text.split(whereSeparator: \.isWhitespace)`). -/
def signerKeysOf (text : String) : List String :=
  let isSpace (c : Char) := Winnow.Keys.Unicode.isWhitespaceOrNewline c && c.toNat != 0x200B
  (text.split isSpace).toList.map (·.toString) |>.filter (!·.isEmpty)

def Network.bitcoin : Network → Winnow.Tx.BitcoinNetwork
  | .mainnet => .mainnet | .signet => .signet | .regtest => .regtest

/-- `SignerLabel.fingerprint(of:network:)`: "6824f543", or "?" for text that is not a signer key. -/
def keyFingerprint (key : String) (network : Network) : String :=
  match Winnow.MultisigAccount.signerKey key network.bitcoin with
  | .ok single => (single.origin.map (Winnow.Wallet.hex8 ·.fingerprint)).getD "?"
  | .error _ => "?"

/-- SignerKeysAddView's `parseError`: why the pasted text is not a signer, if it is not. -/
def signerKeysError (text : String) (network : Network) : Option String :=
  (signerKeysOf text).findSome? fun key =>
    match Winnow.MultisigAccount.signerKey key network.bitcoin with
    | .ok _ => none
    | .error (.account e) => some e.description
    | .error (.named n) => some n

def SignerKeysForm.canSave (f : SignerKeysForm) (network : Network) : Bool :=
  !f.saving && (Winnow.DisplayName.normalized f.name).isSome && !(signerKeysOf f.text).isEmpty &&
    (signerKeysError f.text network).isNone

/-- SignerDetailView's `rename()` on submit and on leaving: only a usable, changed name. -/
def Model.renameSignerCmds (m : Model) : List Cmd :=
  let f := m.signerDetail
  match m.signer? f.id, Winnow.DisplayName.normalized f.name with
  | some s, some n => if n != s.name then [.renameSigner m.generation s.id n] else []
  | _, _ => []

/-- Leave the innermost Signers screen (its state goes with it; the detail screen renames first). -/
def Model.popSigner (m : Model) : Model × List Cmd :=
  match m.routes.getLast? with
  | some (.signer _) =>
    let cs := m.renameSignerCmds
    ({ m with routes := m.routes.dropLast, signerDetail := {} }, cs)
  | some .signerKeysAdd => ({ m with routes := m.routes.dropLast, signerKeys := {} }, [])
  | some .ledgerPair => ({ m with routes := m.routes.dropLast, ledgerPair := {} }, [])
  | some .signers => ({ m with routes := m.routes.dropLast }, [])
  | _ => (m, [])

def stepSigner (msg : SignerMsg) (m : Model) : Model × List Cmd :=
  let g := m.generation
  let keys := m.signerKeys
  match msg with
  | .openSigners => ({ m with routes := m.routes ++ [.signers] }, [.multisigOverview g])
  | .openSigner id =>
    let name := ((m.signer? id).map (·.name)).getD ""
    ({ m with routes := m.routes ++ [.signer id], signerDetail := { id, name } }, [])
  | .openKeysAdd => ({ m with routes := m.routes ++ [.signerKeysAdd], signerKeys := {} }, [])
  | .setKeysName s => ({ m with signerKeys := { keys with name := s } }, [])
  | .pasteKeys => (m, [.paste .signerKeys])
  | .saveKeys =>
    if !keys.canSave m.settings.network then (m, []) else
    ({ m with signerKeys := { keys with saving := true, error := none } },
     [.addSignerKeys g m.settings.advancedMode keys.name keys.text])
  | .setSignerName s => ({ m with signerDetail := { m.signerDetail with name := s } }, [])
  | .renameSigner => (m, m.renameSignerCmds)
  | .removeSigner =>
    match m.routes.getLast? with
    | some (.signer id) => ({ m with signerDetail := { m.signerDetail with error := none } }, [.removeSigner g id])
    | _ => (m, [])
  | .pop => m.popSigner

/-- The backend's signer answers (`onHost` hands them here). -/
def Model.onSignerHost (m : Model) (h : Host) : Model × List Cmd :=
  match h with
  | .signerSaved g _ =>
    if !m.sameWallet g then (m, []) else
    let m' := { m with signerKeys := { m.signerKeys with saving := false } }
    -- `dismiss()`
    let m' := if m'.routes.getLast? == some .signerKeysAdd then { m' with routes := m'.routes.dropLast, signerKeys := {} } else m'
    (m', [.multisigOverview m.generation])
  | .signerRenamed g _ => if m.sameWallet g then (m, [.multisigOverview m.generation]) else (m, [])
  | .signerRemoved g id =>
    if !m.sameWallet g then (m, []) else
    let m' := if m.routes.getLast? == some (.signer id) then { m with routes := m.routes.dropLast, signerDetail := {} } else m
    (m', [.multisigOverview m.generation])
  | _ => (m, [])

/-! ## View -/

/-- `SignersSection`'s summary: "1 Ledger, 2 saved", or "This phone". -/
def signersSummary (o : MultisigOverview) : String :=
  let ledgers := o.ledgers.length
  let saved := o.signers.length - ledgers
  let parts := (if ledgers == 0 then [] else [s!"{ledgers} Ledger{if ledgers == 1 then "" else "s"}"]) ++
    (if saved == 0 then [] else [s!"{saved} saved"])
  if parts.isEmpty then "This phone" else ", ".intercalate parts

/-- Settings → "Signers" (Advanced mode only, after Backup). -/
def signersSection (m : Model) : H :=
  .section "" "Pair a Ledger once, and save the keys other people send; multisig accounts under Wallet are built from them."
    [.row [.identified "signersButton" (navLink "Signers" (some (.signer .openSigners)) (symbol := "person.2")), .spacer,
           Html.tone .secondary (body (signersSummary m.multisig))]]

/-- `SignerRow`. -/
def signerRow (s : SignerInfo) (action : Option Msg) (id : String := s!"signerRow-{s.id}") : H :=
  .col [.identified id (navLink s.name action),
        caption (s.keysText ++ (if s.keys.length > 1 then " · one signer" else ""))]

/-- SignersView. -/
def signersSections (m : Model) : List H :=
  let o := m.multisig
  (match o.signerNotice with
   | some n => [.section "" "" [.identified "signerStorageNotice" (body n)]]
   | none => []) ++
  [ .section "This phone" "Send this key to whoever builds an account you join. To count this phone and its Ledger as one signer of their account, send both keys together from Wallet → Multisig → Join an account."
      (match o.keyExpression with
       | some key =>
         [ .identified "signersOwnFingerprint" (.labeled "Fingerprint" (o.ownFingerprint.getD "?"))
         , literalRow m "signers.own" key "signersOwnKeyCopy" ]
       | none => [caption "This wallet has no shareable account key."])
  , .section "Ledgers" "Paired once, a Ledger can be a member of any account you build, or sign with this phone as one member; the account is then approved on its screen."
      ((o.ledgers.map fun s => signerRow s (some (.signer (.openSigner s.id)))) ++
       [.identified "signersPairLedgerButton" (navLink "Pair a Ledger" (some (.multisig .openLedgerPair)) (symbol := "plus.circle"))])
  , .section "Other people's keys" "One key, or a phone's and its Ledger's sent together, which then count as one signer."
      ((o.savedKeys.map fun s => signerRow s (some (.signer (.openSigner s.id)))) ++
       [.identified "signersAddKeysButton" (navLink "Save keys someone sent" (some (.signer .openKeysAdd)) (symbol := "key"))]) ] ++
  errorSection m.signerDetail.error

/-- SignerDetailView. -/
def signerDetailSections (m : Model) (id : String) : List H :=
  match m.signer? id with
  | none => [.section "" "" [caption "This signer is no longer on this phone."]] ++ errorSection m.signerDetail.error
  | some s =>
    [ .section ""
        (if s.isLedger then "A paired Ledger. Its key sits at the Ledger's multisig path on this network."
         else s!"{if s.keys.length == 1 then "A key" else s!"{s.keys.length} keys that sign together,"} someone sent you.")
        [.identified "signerNameField"
          (.input .plain "" "Name" m.signerDetail.name (fun t => .signer (.setSignerName t)) (some (.signer .renameSigner)))]
    , .section "Keys" "" (s.keys.map fun k => literalRow m s!"signer.key.{k}" k s!"signerKeyCopy-{String.ofList (k.toList.drop (k.length - 8))}")
    , .section "" "Accounts already built with it are not changed."
        [.identified "signerRemoveButton" (.button "Remove signer" .destructive (some (.signer .removeSigner)))] ] ++
    errorSection m.signerDetail.error

/-- LedgerPairView ("Pair a Ledger"): files the Ledger's key among the signers. -/
def ledgerPairSections (m : Model) : List H :=
  let f := m.ledgerPair
  [ .section "" "What this phone calls the Ledger, such as Nano X."
      [.identified "ledgerNameField" (.input .plain "" "Name" f.name (fun s => .multisig (.setLedgerName s)) none)]
  , .section "Steps" ""
      [ body "1. Unlock the Ledger and open its Bitcoin app, version 2.1.2 or later (Bitcoin Test on signet)."
      , body "2. Tap Pair. The first time, confirm the same pairing code on the phone and the Ledger."
      , body "3. The Ledger's multisig key is saved here. Nothing is approved on the Ledger until an account uses it." ]
  , .section "" ""
      ([.identified "ledgerPairButton"
         (.button (if f.pairing then "Pairing…" else "Pair") .primary (if f.pairing || !f.nameIsUsable then none else some (.multisig .pairLedger)))] ++
       (if f.pairing then [.progress ""] else [])) ] ++
  (match f.error with
   | some e => [.section "" "" [.identified "ledgerPairError" (body e)]]
   | none => [])

/-- SignerKeysAddView ("Save keys"). -/
def signerKeysSections (m : Model) : List H :=
  let f := m.signerKeys
  let network := m.settings.network
  let keys := signerKeysOf f.text
  [ .section "" "Whose keys these are, such as Bob, or Bob's phone and Ledger."
      [.identified "signerKeysNameField" (.input .plain "" "Name" f.name (fun s => .signer (.setKeysName s)) none)]
  , .section "" "Another Winnow shows its key under Wallet → Multisig → Join an account → This phone's key, alone or together with its Ledger's. Any signer's key works: [fingerprint/path]xpub…/<0;1>/*."
      ([.identified "signerKeysPasteButton" (.button "Paste keys" .plain (some (.signer .pasteKeys)))] ++
       (keys.map fun k => .col [caption (keyFingerprint k network), literal k]) ++
       (match signerKeysError f.text network with
        | some e => [.identified "signerKeysError" (body e)]
        | none => if keys.length > 1 then [caption s!"{keys.length} keys that always sign together: one signer."] else [])) ] ++
  (match f.error with
   | some e => [.section "" "" [.identified "signerKeysError" (body e)]]
   | none => [])

def signerKeysScreen (m : Model) (inner : List H) : H :=
  let f := m.signerKeys
  .screen "Save keys" (some (.signer .pop))
    ([ .toolbar [.identified "signerKeysSaveButton"
                   (.button (if f.saving then "Saving…" else "Save") .primary
                      (if f.canSave m.settings.network then some (.signer .saveKeys) else none))]
     , .list (signerKeysSections m) ] ++ inner)

/-- SignerPickerSheet ("Add a member"): a paired Ledger, keys someone sent, an account already on this
phone (its keys, signing as its policy says), or keys pasted now. A key already among the members
cannot be picked twice, except this phone's own inside a whole account, which moves into it. -/
def signerPickerSheet (m : Model) (inner : List H) : H :=
  let f := m.multisigBuild
  let used := f.usedKeys
  let whole := f.pickInto.isNone
  let phone := m.multisig.keyExpression
  let signerButton (s : SignerInfo) : H :=
    signerRow s (if s.keys.any used.contains then none else some (.multisig (.pickSigner s.id))) s!"signerPick-{s.id}"
  formSheet "Add a member" (some .closeSheet) [closeBar "Cancel"]
    [ .section "Ledgers" ""
         ((if m.multisig.ledgers.isEmpty then [caption "None paired. Pair one under Settings → Signers."] else []) ++
          m.multisig.ledgers.map signerButton)
     , .section "Saved keys" ""
         ((if m.multisig.savedKeys.isEmpty then
             [caption "None saved. Save keys someone sent under Settings → Signers, or paste them below."] else []) ++
          m.multisig.savedKeys.map signerButton)
     , .section "Accounts on this phone" "A whole account as one member: its keys sign for it as its own policy says, every key of a 2-of-2, any 2 of a 2-of-3. This phone's key moves into it. Its own recovery path stays with it, and a nested account cannot be one member yet."
         ((if m.multisig.accounts.isEmpty then [caption "None yet."] else []) ++
          (m.multisig.accounts.filter (·.policy.isSome)).map fun a =>
            let eligible := pickerAccountEligible a whole
            let taken := a.signerExpressions.any fun k => some k != phone && used.contains k
            .col [.identified s!"signerPickAccount-{a.id}"
                    (navLink a.name (if eligible && !taken then some (.multisig (.pickAccount a.id)) else none)),
                  caption (pickerAccountText a eligible)])
     , .section "" "One key, or several that always sign together, as another Winnow shows them under Join an account."
         ([.identified "signerPickerPasteButton" (.button "Paste keys from the clipboard" .plain (some (.multisig .pasteMemberKeys)))] ++
          (match f.pasteError with
           | some e => [.identified "signerPickerPasteError" (body e)]
           | none => [])) ] inner

end WinnowApp
