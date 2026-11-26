module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open Blocks.Example
open Join (model)
open Join.Finite (Table)

-- Entry 4, header 2, true arm 5 → 6, false arm 0, merge 3, latch 1.
private def source (trueNext : Fin 7) : Source Arithmetic regs num 7 :=
  fun i =>
    if i = 4 then
      ⟨[⟨_, _, x, .copy, .cons stride .nil⟩], .transfer (.jump 2)⟩
    else if i = 2 then
      ⟨[⟨_, _, again, .positive, .cons x .nil⟩], .branch again (.jump 5) (.jump 0)⟩
    else if i = 5 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩], .transfer (.jump trueNext)⟩
    else if i = 6 then
      ⟨[⟨_, _, y, .add, .cons y (.cons stride .nil)⟩, ⟨_, _, x, .copy, .cons saved .nil⟩],
        .transfer (.jump 3)⟩
    else if i = 0 then
      ⟨[⟨_, _, y, .add, .cons y (.cons y .nil)⟩, ⟨_, _, x, .copy, .cons stride .nil⟩],
        .transfer (.jump 3)⟩
    else if i = 3 then
      ⟨[⟨_, _, y, .copy, .cons y .nil⟩], .transfer (.jump 1)⟩
    else
      ⟨[⟨_, _, counter, .pred, .cons counter .nil⟩, ⟨_, _, again, .positive, .cons counter .nil⟩],
        .branch again (.jump 2) (.ret y)⟩

private abbrev good := source 6
private def checked : Program good 4 := (check good 4).get (by rfl)

example : check (source 5) 4 = none := rfl
example : (checked.armPath 0).blocks = [5, 6] := rfl
example : (checked.armPath 1).blocks = [0] := rfl
example : (Table.incoming checked.stage.table (0 : Fin 2)).get y = .output ⟨1, by decide⟩ .head := rfl
example : (Table.incoming checked.stage.table (1 : Fin 2)).get y = .output ⟨0, by decide⟩ .head := rfl

private def initial := (good 4).body.eval arithmetic (input 3)
private def trace := checked.trace arithmetic 3 initial

example : trace.map checked.predecessor = [6, 0, 6] := rfl
example : trace.map checked.activationCost = [5, 4, 5] := rfl
example : checked.sourceVisits arithmetic 2 (input 3) = 10 := rfl
example : checked.sourceVisits arithmetic 3 (input 3) = 15 := rfl
example : checked.sourceVisits arithmetic 4 (input 3) = 15 := rfl

example : checked.lower.run (model arithmetic) 2 (input 3) = none :=
  checked.lower_run arithmetic 2 (input 3)

private theorem returned :
    checked.lower.run (model arithmetic) 3 (input 3) = some (.cons (22 : Nat) .nil) :=
  checked.lower_run arithmetic 3 (input 3)

example : good.runFrom arithmetic 14 4 (input 3) = none :=
  checked.run_at arithmetic 3 14 (input 3) (22 : Nat) returned

example : good.runFrom arithmetic 15 4 (input 3) = some (22 : Nat) :=
  checked.run_at arithmetic 3 15 (input 3) (22 : Nat) returned

example : checked.lower.Returns (model arithmetic) (input 3) (.cons (22 : Nat) .nil) :=
  (checked.returns_iff arithmetic (input 3) (22 : Nat)).mpr ⟨15, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
