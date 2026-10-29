import Oracle.Wallet
import Oracle.WalletScenario
import Oracle.WalletPeople
open Lean in
/-- The pure ops, plus the file-system ops of `ExportStagingFile` (answered in `IO`). -/
partial def loop (pureOps : Std.HashMap String Oracle.Handler) (io : Std.HashMap String (Json → IO Json))
    (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := line.trimAscii.copy
  let reply ← match Json.parse line with
    | .ok j => match (j.getObjValAs? String "op").toOption.bind (io[·]?) with
      | some h => h j
      | none => pure (Oracle.answer pureOps line)
    | .error _ => pure (Oracle.answer pureOps line)
  stdout.putStrLn reply.compress
  stdout.flush
  loop pureOps io stdin stdout

def main : IO Unit := do
  loop (Std.HashMap.ofList (Oracle.walletOps ++ Oracle.WalletPeople.ops)) (Std.HashMap.ofList (Oracle.walletIOOps ++ Oracle.WalletScenario.ops ++ Oracle.WalletPeople.ioOps)) (← IO.getStdin) (← IO.getStdout)
