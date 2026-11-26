module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain

open Blocks.Example

-- Original order is entry 2 → header 0 → internal 3 → latch 1.
private def source (middleNext feedback : Fin 4) (exit : Destination regs num 4) :
    Source Arithmetic regs num 4 :=
  fun id =>
    if id = 2 then
      ⟨[⟨_, _, x, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump 0)⟩
    else if id = 0 then
      ⟨[⟨_, _, saved, .copy, .cons x .nil⟩, ⟨_, _, x, .copy, .cons y .nil⟩], .transfer (.jump 3)⟩
    else if id = 3 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump middleNext)⟩
    else
      ⟨[⟨_, _, y, .add, .cons saved (.cons y .nil)⟩,
        ⟨_, _, counter, .pred, .cons counter .nil⟩,
        ⟨_, _, again, .positive, .cons counter .nil⟩], .branch again (.jump feedback) exit⟩

private abbrev good := source 1 0 (.ret y)
private def checked : Program good 2 := (check good 2).get (by rfl)

example : checked.blockOrder = [2, 0, 3, 1] := rfl
example : checked.predecessor .entry = 2 := rfl
example : checked.predecessor .backedge = 1 := rfl
example : checked.activationLength = 3 := rfl

-- The first case circles through two unconditional jumps. The others use
-- a false transfer instead of returning, or return to the wrong header.
example : check (source 0 0 (.ret y)) 2 = none := rfl
example : check (source 1 0 (.jump 3)) 2 = none := rfl
example : check (source 1 3 (.ret y)) 2 = none := rfl

-- The second write to y is producer 3, after the internal block's write.
example : (checked.lower.phiInputs .entry).get y = .arg y := rfl
example : (checked.lower.phiInputs .backedge).get y = .output ⟨3, by decide⟩ .head := rfl
example : checked.lower.phiInputs .backedge = checked.feedbackColumn :=
  checked.feedback_column

private def firstHeader := checked.lower.initial arithmetic (input 3)
private def secondHeader := checked.fuse.latch arithmetic .backedge (input 3) firstHeader

-- The latch reads y = 7 from the internal block, sets y = 14, and the
-- next header reads that feedback value.
example : firstHeader.get y = (5 : Nat) := rfl
example : ((good 3).body.eval arithmetic firstHeader).get y = (7 : Nat) := rfl
example : secondHeader.get y = (14 : Nat) := rfl
example : ((good 0).body.eval arithmetic secondHeader).get x = (14 : Nat) := rfl

example : good.runFrom arithmetic 9 2 (input 3) = none := rfl
example : good.runFrom arithmetic 10 2 (input 3) = some (37 : Nat) := rfl
example : checked.lower.evalBackedges arithmetic 1 (input 3) = none := rfl
example : checked.lower.evalBackedges arithmetic 2 (input 3) = some (37 : Nat) := rfl
example : good.runFrom arithmetic 10 2 (input 3) =
    checked.lower.evalBackedges arithmetic 2 (input 3) :=
  checked.lower_budget arithmetic (input 3) 2 0 (by decide)
example : checked.lower.Returns arithmetic (input 3) (37 : Nat) :=
  (checked.returns_iff arithmetic (input 3) (37 : Nat)).mpr ⟨10, rfl⟩

private def two : Source Arithmetic regs num 2 :=
  fun id => if id = 0 then
    ⟨program.preheader.body, .transfer (.jump 1)⟩
  else
    ⟨program.header.body, .branch program.header.test (.jump 1) (.ret program.header.result)⟩

private def three : Tail.Program Arithmetic regs num :=
  ⟨program.preheader.body, program.header.body.take 2,
    .branch (program.header.body.drop 2) program.header.test program.header.result⟩

private def checkedTwo := (check two 0).get (by rfl)
private def checkedThree := (check three.source 0).get (by rfl)

example : checkedTwo.activationLength = 1 := rfl
example : checkedThree.activationLength = 2 := rfl
example : checkedTwo.lower.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : checkedThree.lower.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : two.runFrom arithmetic 4 0 (input 3) = some (29 : Nat) := rfl
example : three.source.runFrom arithmetic 7 0 (input 3) = some (29 : Nat) := rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain
