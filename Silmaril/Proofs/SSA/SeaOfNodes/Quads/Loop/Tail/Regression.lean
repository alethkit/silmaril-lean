module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail

open Blocks.Example

private def source (entryTarget : Fin 3) : Source Arithmetic regs num :=
  fun i =>
    if i = 0 then
      ⟨[⟨_, _, x, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump entryTarget)⟩
    else if i = 1 then
      ⟨[⟨_, _, saved, .copy, .cons x .nil⟩, ⟨_, _, x, .copy, .cons y .nil⟩], .transfer (.jump 2)⟩
    else
      ⟨[⟨_, _, y, .add, .cons saved (.cons y .nil)⟩,
        ⟨_, _, counter, .pred, .cons counter .nil⟩,
        ⟨_, _, again, .positive, .cons counter .nil⟩], .branch again (.jump 1) (.ret y)⟩

private def checked : Program Arithmetic regs num := (source 1).check.get (by rfl)
private theorem accepted : (source 1).check = some checked := rfl

-- Going directly from entry to latch would give the latch two predecessors.
example : (source 2).check = none := rfl

-- Entry forwards the original y. The backedge sends the latch's first
-- producer, after the two producers of the distinct header block.
example : (checked.lower.phiInputs .entry).get y = .arg y := rfl
example : (checked.lower.phiInputs .backedge).get y = .output ⟨2, by decide⟩ .head := rfl

private def firstHeader := checked.lower.initial arithmetic (input 3)
private def secondHeader := checked.fuse.latch arithmetic .backedge (input 3) firstHeader

example : firstHeader.get y = (5 : Nat) := rfl
example : secondHeader.get y = (12 : Nat) := rfl
example : (checked.header.eval arithmetic secondHeader).get x = (12 : Nat) := rfl

example : (source 1).run arithmetic 2 (input 1) = none := rfl
example : (source 1).run arithmetic 3 (input 1) = some (12 : Nat) := rfl
example : (source 1).run arithmetic 6 (input 3) = none := rfl
example : (source 1).run arithmetic 7 (input 3) = some (29 : Nat) := rfl

example : checked.lower.evalBackedges arithmetic 1 (input 3) = none := rfl
example : checked.lower.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl

example : (source 1).run arithmetic 7 (input 3) = checked.lower.evalBackedges arithmetic 2 (input 3) :=
  Source.lower_run arithmetic (input 3) accepted 7

example : checked.lower.Returns arithmetic (input 3) (29 : Nat) :=
  (Source.returns_iff arithmetic (input 3) accepted (29 : Nat)).mpr ⟨7, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail
