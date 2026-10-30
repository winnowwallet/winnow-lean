/-! # Export staging file

Port of `Sources/WalletCore/Wallet/ExportStagingFile.swift`: a wallet-bundle JSON staged in a unique
`winnow-export-<UUID>` directory for the share sheet, removed on every rewrite and on `remove`, and
`sweep` for directories a crashed process left behind.

Not ported: `protect` (excluded-from-backup resource value and `FileProtectionType.complete`) — those are
iOS file attributes, a platform capability of the shell; and `deinit` (Lean has no finalizers: callers
`remove` explicitly). The temporary directory is an explicit `root`. -/

namespace Winnow

structure ExportStagingFile where
  root : System.FilePath
  url : IO.Ref (Option System.FilePath)

namespace ExportStagingFile

def prefix_ : String := "winnow-export-"

def new (root : System.FilePath) : IO ExportStagingFile := do
  return { root, url := ← IO.mkRef none }

/-- `split(separator: "/").last` (empty pieces dropped), or `wallet.json`. -/
def safeFileName (suggested : String) : String :=
  match ((suggested.splitOn "/").filter (!·.isEmpty)).getLast? with
  | some s => s
  | none => "wallet.json"

def hexUpper (b : UInt8) : String :=
  let d := "0123456789ABCDEF".toList
  String.ofList [d[(b >>> 4).toNat]!, d[(b &&& 15).toNat]!]

/-- `UUID().uuidString`: a random (version 4) UUID, upper-case. -/
def uuidString : IO String := do
  let b ← IO.getRandomBytes 16
  let b := b.set! 6 ((b[6]! &&& 0x0F) ||| 0x40) |>.set! 8 ((b[8]! &&& 0x3F) ||| 0x80)
  let h := b.toList.map hexUpper
  let part (i n : Nat) := String.join ((h.drop i).take n)
  return s!"{part 0 4}-{part 4 2}-{part 6 2}-{part 8 2}-{part 10 6}"

def remove (s : ExportStagingFile) : IO Unit := do
  let some u ← s.url.get | return
  if let some dir := u.parent then
    try IO.FS.removeDirAll dir catch _ => pure ()
  s.url.set none

/-- Writes `contents` (atomically: a sibling temp file renamed into place) and returns its path. -/
def write (s : ExportStagingFile) (contents : String) (suggestedName : String) : IO System.FilePath := do
  s.remove
  let dir := s.root / (prefix_ ++ (← uuidString))
  try
    IO.FS.createDirAll dir
    let file := dir / safeFileName suggestedName
    let tmp := dir / (".tmp-" ++ (← uuidString))
    IO.FS.writeFile tmp contents
    IO.FS.rename tmp file
    s.url.set (some file)
    return file
  catch e =>
    try IO.FS.removeDirAll dir catch _ => pure ()
    s.url.set none
    throw e

/-- Removes every `winnow-export-*` entry under `root`. -/
def sweep (root : System.FilePath) : IO Unit := do
  let entries ← try root.readDir catch _ => return
  for e in entries do
    if e.fileName.startsWith prefix_ then
      try
        if ← e.path.isDir then IO.FS.removeDirAll e.path else IO.FS.removeFile e.path
      catch _ => pure ()

end ExportStagingFile
end Winnow
