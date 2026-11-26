module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open Diamond.MLIR.CF.Example (input width)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example
  (fullHeader report runAt skipsMerge source strideUse)

private def targets : Targets source 0 := ((compile source 0).toOption).get (by rfl)

example : Nested.check source 0 = some targets.program := compile_origin (by rfl)
example : targets.prepared.positions = [1, 0] := rfl
example : strideUse targets = some (3, true) := rfl
example : (report targets).predecessors = [3, 2, 4] := rfl

example : compile skipsMerge 0 = .error .shape := compile_shape_refusal rfl
example : (Nested.check fullHeader 0).isSome = true := rfl
example : compile fullHeader 0 = .error .headerProjection := rfl

example : (report targets).guardAndExit = [some (true, 7), some (true, 8), some (false, 16)] := by
  simp only [report, List.map_cons, List.map_nil, Targets.numbered_packet]
  rfl

example : runAt targets 14 15 3 = (some 16, some 16, some 16) := by
  unfold runAt
  rw [targets.cf_run input 14, targets.numbered_run input 3]
  rfl

example : runAt targets 13 14 2 = (none, none, none) := by
  unfold runAt
  rw [targets.cf_run input 13, targets.numbered_run input 2]
  rfl

example : (∃ cfFuel, targets.cf.run evalOp cfFuel (encodeValues input) = some (.cons (16 : Word width) .nil)) ∧
    targets.numbered.Returns (Join.model model) input (.cons (16 : Word width) .nil) := by
  have agreement := targets.returns_iff input (16 : Word width)
  exact ⟨agreement.1.mpr ⟨14, rfl⟩, agreement.2.mpr ⟨14, rfl⟩⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends
