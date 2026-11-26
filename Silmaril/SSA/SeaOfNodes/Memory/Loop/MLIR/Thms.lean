module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.Correctness

/-! Exact finite budgets and partial observations of the emitted memory loop. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR

open RVSDG (Tuple)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)
open Memory.Diamond.MLIR.Finite hiding entryTypes encodeEntry lower

variable {args : List ValueSort}
variable (p : Profile) (graph : Graph args) (input : Tuple (Val p.cells) args) (initial : Heap p.cells)

/-- Entry, the final body and test, and exit cost four block ticks. Each
completed backedge adds a body and test. This characterizes every target
return, including the entire encoded heap. -/
theorem lower_run_eq_some (fuel : Nat) (output : Env (resultTypes p)) :
    (lower p graph).run evalOp fuel (encodeEntry p input initial) = some output ↔
      ∃ count word final, 2 * count + 4 ≤ fuel ∧ graph.ReturnsAfter input initial count word final ∧
        output = encodeResult p word final :=
  Proofs.lower_run_eq_some p graph input initial fuel output

/-- The exact native word and heap are returned at some finite budget
if and only if the typed CFG returns their encoding at some finite budget. -/
theorem lower_returns_iff (word : Word) (final : Heap p.cells) :
    graph.Returns input initial word final ↔
      ∃ fuel, (lower p graph).run evalOp fuel (encodeEntry p input initial) = some (encodeResult p word final) :=
  Proofs.lower_returns_iff p graph input initial word final

/-- The existing partial CF denotation is precisely the encoding of the
native partial result. -/
theorem lower_denotePart :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower p graph)).denotePart evalOp (encodeEntry p input initial) =
      (graph.denote input initial).map (fun result => Outcome.returned (encodeResult p result.1 result.2)) :=
  Proofs.lower_denotePart p graph input initial

/-- No finite budget returns exactly when the native partial observation is
undefined. -/
theorem lower_diverges_iff :
    (lower p graph).Diverges evalOp (encodeEntry p input initial) ↔ ¬ (graph.denote input initial).Dom := by
  rw [← Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_diverges_iff,
    ← Silmaril.MLIR.CF.SwitchAssert.Cfg.denotePart_eq_none_iff, lower_denotePart, Part.eq_none_iff']
  rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR
