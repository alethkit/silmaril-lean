module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune

open SeaOfNodes.Diamond (Ty dataPorts)
open Blocks.Example
open Blocks.Prune (Mask)
open Example (source)
open Join (model)

private abbrev good := source 6
private def full : Program good 4 := (check good 4).get (by rfl)
private abbrev keep := carriedMask full
private def smaller : Checked full keep := (prune full).get (by rfl)

-- The split and latch both assign again before using it. The old predicate
-- therefore never needs to cross the θ boundary.
example : keep.rename again = none := rfl
example : keep.kept.length = 5 := rfl

-- x is read in the header. saved reaches the long arm, which uses it to
-- change the predicate on the next iteration.
example : checkMask full (Mask.ofSlots (fun i => i != 1) regs) = none := rfl
example : checkMask full (Mask.ofSlots (fun i => i != 3) regs) = none := rfl

private def carrierWidth : {ins outs : List (Ty Unit)} →
    RVSDG.NestedTheta.Kind (Join.Opcode Arithmetic) ins outs → Option Nat
  | _, _, .theta carried => some carried.length
  | _, _, .base _ => none

private def thetaWidth {sigs : List (List (Ty Unit))}
    (graph : RVSDG.NestedTheta.Graph (Join.Opcode Arithmetic) (dataPorts regs) [] sigs [.value num])
    (site : Fin sigs.length) : Option Nat :=
  match graph with
  | .region nodes _ _ => carrierWidth (nodes site).kind

example : thetaWidth full.lower ⟨1, by decide⟩ = some 6 := rfl
example : thetaWidth smaller.lower ⟨1, by decide⟩ = some 5 := rfl

private def initialBank := (good 4).body.eval arithmetic (input 3)

example : (smaller.trace arithmetic 3 (keep.project initialBank)).map full.predecessor = [6, 0, 6] := by
  rw [smaller.trace_agrees]
  rfl

example : smaller.lower.run (model arithmetic) 2 (input 3) = none :=
  smaller.lower_run arithmetic 2 (input 3)

private theorem returned : smaller.lower.run (model arithmetic) 3 (input 3) = some (.cons (22 : Nat) .nil) :=
  smaller.lower_run arithmetic 3 (input 3)

example : good.runFrom arithmetic 14 4 (input 3) = none :=
  smaller.run_at arithmetic 3 14 (input 3) (22 : Nat) returned

example : smaller.lower.Returns (model arithmetic) (input 3) (.cons (22 : Nat) .nil) :=
  (smaller.returns_iff arithmetic (input 3) (22 : Nat)).mpr ⟨15, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune
