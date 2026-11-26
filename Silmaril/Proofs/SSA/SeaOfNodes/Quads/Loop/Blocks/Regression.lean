module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks

open Example

-- The preheader creates x; the feedback defines both x and y in the
-- header's own producer scope. The untouched slot reads a pending port.
example : ((program.lower.phiInputs .entry).get x).producer = some 0 := rfl
example : ((program.lower.phiInputs .backedge).get x).producer = some 1 := rfl
example : ((program.lower.phiInputs .backedge).get y).producer = some 2 := rfl
example : (program.lower.phiInputs .backedge).get stride = .arg (carryPort stride ports) := rfl

private def first := program.latch arithmetic .entry (input 3) (input 3)
private def second := program.latch arithmetic .backedge (input 3) first
private def third := program.latch arithmetic .backedge (input 3) second

example : first = bank 3 7 5 0 2 false := rfl
example : second = bank 2 5 12 7 2 true := rfl
example : third = bank 1 12 17 5 2 true := rfl

-- A differing feedback value is used on the next activation. Zero budget
-- still permits an immediate return after the preheader and first header.
example : program.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl
example : program.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.lower.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : program.lower.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks
