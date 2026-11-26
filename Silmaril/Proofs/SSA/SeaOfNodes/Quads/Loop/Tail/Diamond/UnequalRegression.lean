module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open Blocks.Example
open Example (source)
open Join (model)
open Join.Finite (Table)

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
