module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune

open RVSDG (Tuple)
open Example

private abbrev live := carriedMask program

private def pruned : PrunedGraph program live :=
  (prune program).get (by rfl)

private theorem accepted : pruneWith program live = some pruned := rfl

-- The scratch and predicate are read only after being overwritten. The
-- original stride is only read in the preheader. Both accumulators stay.
example : live.kept = [num, num, num] := rfl
example : live.rename saved = none := rfl
example : live.rename again = none := rfl
example : live.rename stride = none := rfl
example : live.rename x = some (.tail .head) := rfl
example : live.rename y = some (.tail (.tail .head)) := rfl

-- The old value of y is read before its overwrite, so dropping it fails.
example : pruneWith program (Mask.ofSlots (fun i => i != 2) regs) = none := rfl

example : pruned.initial arithmetic (input 3) =
    .cons (3 : Nat) (.cons (7 : Nat) (.cons (5 : Nat) .nil)) := rfl
example : pruned.step arithmetic (input 3) (pruned.initial arithmetic (input 3)) =
    .inr (.cons (2 : Nat) (.cons (5 : Nat) (.cons (12 : Nat) .nil))) := rfl

example : pruned.evalBackedges arithmetic 0 (input 3) = none := rfl
example : pruned.evalBackedges arithmetic 1 (input 3) = none := rfl
example : pruned.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : pruned.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl

example : pruned.Returns arithmetic (input 3) (29 : Nat) :=
  (returns_iff program live accepted arithmetic (input 3) (29 : Nat)).mpr ⟨2, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune
