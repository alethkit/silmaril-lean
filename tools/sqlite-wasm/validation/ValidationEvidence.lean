module

public import SqliteWasm.WholeModule
public import SqliteWasm.ValidationInputs
import SqliteWasmArtifactEntries

namespace SqliteWasm.ValidationEvidence

open Silmaril.Wasm Silmaril.Wasm.Validation

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

sqlite_check_eq resolvedSignatures :
    (bodyInputs? sqlite).map (fun inputs => inputs.signatures.length) = some 1533

private def checkPrefix (m : Module) (count : Nat) : Bool :=
  (bodyInputs? m).any fun inputs =>
    allPairs (defaultCheckers.func inputs.context) (m.funcs.take count) (inputs.signatures.take count)

sqlite_check_eq prefixChecked : checkPrefix sqlite 32 = true

public theorem firstBodies :
    ∃ inputs, bodyInputs? sqlite = some inputs ∧
      List.Forall₂ (FuncOk inputs.context) (sqlite.funcs.take 32) (inputs.signatures.take 32) := by
  have ok := prefixChecked
  unfold checkPrefix at ok
  cases prepared : bodyInputs? sqlite with
  | none => simp [prepared] at ok
  | some inputs =>
    refine ⟨inputs, rfl, allPairs_sound defaultCheckers_sound.func ?_⟩
    simpa [prepared] using ok

private def checkBodyAt? (m : Module) (ordinal : Nat) : Option Bool := do
  let inputs ← bodyInputs? m
  let f ← m.funcs[ordinal]?
  let signature ← inputs.signatures[ordinal]?
  return defaultCheckers.func inputs.context f signature

sqlite_check_eq versionChecked : checkBodyAt? sqlite 266 = some true

public theorem versionBody : BodyValidAt sqlite 266 := by
  have ok := versionChecked
  simp only [checkBodyAt?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ok
  obtain ⟨inputs, prepared, f, body, signature, resolved, checked⟩ := ok
  exact ⟨inputs, f, signature, prepared, body, resolved, defaultCheckers_sound.func checked⟩

end SqliteWasm.ValidationEvidence
