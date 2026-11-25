module

import Silmaril.Wasm.Examples.Sha256Round.Thms
meta import Silmaril.Wasm.Examples.Sha256Round.Defs
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

open Silmaril.Wasm.Examples.Sha256Round
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded.Exec
open Lean Elab Command

private def abcRound0 : Input :=
  ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
    0x5be0cd19, 0x428a2f98, 0x61626380⟩

example : (runI (fun _ _ _ _ => false) fuel (entry abcRound0 ({} : Store Unit) {})).1.code =
    [constI32 0x5d6aebcd] := by
  have expected : (Silmaril.Crypto.SHA256.Kernel.round abcRound0.a abcRound0.b abcRound0.c 0
      abcRound0.e abcRound0.f abcRound0.g abcRound0.h abcRound0.k abcRound0.w).1 =
      0x5d6aebcd := by decide +kernel
  rw [run_fixture (d := 0)]
  exact congrArg (fun out => [constI32 out]) expected

run_cmd do
  let checked := [``decode_fixture, ``run_fixture, ``steps_fixture]
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for decl in checked do
    let axioms ← collectAxioms decl
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "{decl} transitively uses {axiomName}"
    logInfo m!"{decl} transitive axioms {axioms.toList}"

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected the rebuilt Wasm path")
  let rebuilt ← IO.FS.readBinFile path
  if rebuilt.data != fixture.data then
    throw (IO.userError "rebuilt Wasm differs from the Lean fixture")
  IO.println s!"Rebuilt Wasm matches all {rebuilt.size} pinned octets"
