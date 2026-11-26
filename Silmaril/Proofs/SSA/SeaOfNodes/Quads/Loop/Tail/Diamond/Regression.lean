module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open Blocks.Example
open Join (model)
open Join.Finite (Table)

-- Entry 4, split 2, true 5, false 0, merge 3, latch 1.
private def source (falseTarget backedge : Fin 6) : Source Arithmetic regs num :=
  fun i =>
    if i = 4 then
      ⟨[⟨_, _, x, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump 2)⟩
    else if i = 2 then
      ⟨[⟨_, _, saved, .pred, .cons counter .nil⟩, ⟨_, _, again, .positive, .cons saved .nil⟩],
        .branch again (.jump 5) (.jump 0)⟩
    else if i = 5 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump 3)⟩
    else if i = 0 then
      ⟨[⟨_, _, saved, .copy, .cons y .nil⟩, ⟨_, _, y, .add, .cons saved (.cons x .nil)⟩],
        .transfer (.jump falseTarget)⟩
    else if i = 3 then
      ⟨[⟨_, _, x, .copy, .cons y .nil⟩], .transfer (.jump 1)⟩
    else
      ⟨[⟨_, _, counter, .pred, .cons counter .nil⟩, ⟨_, _, again, .positive, .cons counter .nil⟩],
        .branch again (.jump backedge) (.ret x)⟩

private abbrev good := source 3 2
private def checked : Program good 4 := (check good 4).get (by rfl)

example : checked.predecessor 0 = 5 := rfl
example : checked.predecessor 1 = 0 := rfl
example : check (source 1 2) 4 = none := rfl
example : check (source 3 3) 4 = none := rfl

-- The two incoming y slots name different arm-local producers.
example : (Table.incoming checked.stage.table (0 : Fin 2)).get y = .output ⟨0, by decide⟩ .head := rfl
example : (Table.incoming checked.stage.table (1 : Fin 2)).get y = .output ⟨1, by decide⟩ .head := rfl

private def first := (good 4).body.eval arithmetic (input 2)
private def next := checked.nextBank arithmetic first

example : checked.stage.choice.eval ((good 2).body.eval arithmetic first) = 0 := rfl
example : checked.stage.choice.eval ((good 2).body.eval arithmetic next) = 1 := rfl
example : next.get y = (7 : Nat) := rfl
example : next.get x = (7 : Nat) := rfl
example : (checked.nextBank arithmetic next).get x = (14 : Nat) := rfl

example : (checked.thetaBody.run (model arithmetic) 1 first).map (fun packet => packet.get (.tail x)) =
    some (7 : Nat) := by
  rw [checked.activation_run]
  rfl

example : good.runFrom arithmetic 8 4 (input 2) = none := rfl
example : good.runFrom arithmetic 9 4 (input 2) = some (14 : Nat) := rfl
example : good.runFrom arithmetic 5 4 (input 1) = some (12 : Nat) := rfl

example : checked.lower.run (model arithmetic) 1 (input 2) = none :=
  checked.lower_run arithmetic 1 0 (by decide) (input 2)
example : checked.lower.run (model arithmetic) 2 (input 2) = some (.cons (14 : Nat) .nil) :=
  checked.lower_run arithmetic 2 0 (by decide) (input 2)
example : checked.lower.run (model arithmetic) 1 (input 1) = some (.cons (12 : Nat) .nil) :=
  checked.lower_run arithmetic 1 0 (by decide) (input 1)

example : checked.lower.Returns (model arithmetic) (input 2) (.cons (14 : Nat) .nil) :=
  (checked.returns_iff arithmetic (input 2) (14 : Nat)).mpr ⟨9, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
