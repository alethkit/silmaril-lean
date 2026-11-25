module

public import Silmaril.Wasm.Examples.Sha256Round.Defs
import Silmaril.Proofs.Wasm.Examples.Sha256Round.Run

public section
namespace Silmaril.Wasm.Examples.Sha256Round

open Execution.Core SingleThreaded SingleThreaded.Det SingleThreaded.Exec
open Silmaril.Crypto.SHA256.Kernel (Word round)

/-- The pinned module exports a function with nine i32 parameters, one i32
result, no additional locals, and the exact body executed by the theorem. -/
theorem decode_fixture :
    exportedRound? fixture = some (signature, ⟨⟨0⟩, [], body⟩) :=
  Proofs.Wasm.Examples.Sha256Round.decode_fixture

/-- Starting with the parameters already in the Core frame, the verified
interpreter stops with the new working word a and preserves the frame and store. -/
theorem run_fixture {H : Type} (o : GrowOracle) (x : Input) (d : Word) (s : Store H)
    (mi : ModuleInst) :
    runI o fuel (entry x s mi) =
      (⟨s, x.frame mi, [constI32 (round x.a x.b x.c d x.e x.f x.g x.h x.k x.w).1]⟩, true) :=
  Proofs.Wasm.Examples.Sha256Round.run_fixture o x d s mi

/-- Core small-step consequence for a well-typed entry configuration. -/
theorem steps_fixture {H : Type} (o : GrowOracle) (x : Input) (d : Word) (s : Store H)
    (mi : ModuleInst) (typed : ConfigOk (entry x s mi) [.i32]) :
    Steps (profile o) noHost (entry x s mi)
      ⟨s, x.frame mi, [constI32 (round x.a x.b x.c d x.e x.f x.g x.h x.k x.w).1]⟩ := by
  have steps := runI_steps_typed (o := o) fuel typed
  rwa [run_fixture o x d s mi] at steps

end Silmaril.Wasm.Examples.Sha256Round
