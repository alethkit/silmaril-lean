module
import Silmaril.Formats.Sqlite.VirtualTable.Backed.Thms
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[idx.toNat]!
    unless (`Silmaril.Formats.Sqlite.VirtualTable).isPrefixOf owner ||
        (`Silmaril.Proofs.Formats.Sqlite.VirtualTable).isPrefixOf owner do
      continue
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{name} transitively uses {axiomName}"
    checked := checked + 1
  if checked == 0 then throwError "No virtual table declarations audited"
  logInfo m!"Audited {checked} virtual table declarations for transitive axioms"
