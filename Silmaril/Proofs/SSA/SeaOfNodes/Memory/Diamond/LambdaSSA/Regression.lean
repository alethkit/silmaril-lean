module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA

open SeaOfNodes.Diamond (Projection)
open RVSDG (Origin Port Tuple)
open Isotope.LambdaSSA.Semantics.Region (Eval)

private abbrev args : List ValueSort := [.address, .address, .address, .address, .word, .word]

private def x : Address 4 := 0
private def trueCell : Address 4 := 1
private def falseCell : Address 4 := 2
private def selectedCell : Address 4 := 3
private def initial : Heap 4 := fun address => if address = x then 7 else 0

private def input : Tuple (Val 4) args :=
  .cons x (.cons trueCell (.cons falseCell (.cons selectedCell (.cons (11 : Word) (.cons (33 : Word) .nil)))))

private def oldX : Origin args [[.word]] .word := .output (0 : Fin 1) .head

private def arm (save : Port args .address) (replacement : Port args .word)
    (exported : Origin args [[.word]] .word) : Memory.Graph args :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg save) oldX
      (.store (.latest 1) (.arg .head) (.arg replacement) (.ret (.latest 2) exported)))

private def newTrue : Port args .word := .tail (.tail (.tail (.tail .head)))
private def newFalse : Port args .word := .tail (.tail (.tail (.tail (.tail .head))))

-- Save the selected arm's Return in a separate cell, then load the updated x.
private def diamond (first : Projection) : Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => arm (.tail .head) newTrue oldX
    | .onFalse => arm (.tail (.tail .head)) newFalse (.arg newFalse)
  suffix := .store (.latest 0) (.arg (.tail (.tail (.tail (.tail .head))))) (.arg .head)
    (.load (.latest 1) (.arg (.tail .head)) (.ret (.latest 1) (.output (0 : Fin 1) .head)))

private def afterTrue : Heap 4 := ((initial.write trueCell 7).write x 11).write selectedCell 7
private def afterFalse : Heap 4 := ((initial.write falseCell 7).write x 33).write selectedCell 33

example : (lower (diamond .onFalse)).HasType (entryContext args) [wordPacket] := lower_hasType _

example : (edge (diamond .onTrue) .first).source = .onTrue := rfl
example : (edge (diamond .onFalse) .first).source = .onFalse := rfl
example : (edge (diamond .onFalse) .second).source = .onTrue := rfl
example : (edge (diamond .onFalse) .first).target = (edge (diamond .onFalse) .second).target := rfl
example : edge (diamond .onFalse) .first ≠ edge (diamond .onFalse) .second :=
  (incoming_distinct (diamond .onFalse)).symm

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .first) =
    .br 2 (.pair (.var 10) .unit) :=
  edge_branch (diamond .onFalse) .first

example : (phiView (diamond .onFalse)).table.branch (edge (diamond .onFalse) .second) =
    .br 2 (.pair (.var 2) .unit) :=
  edge_branch (diamond .onFalse) .second

private abbrev targetReturns (order : Projection) (guard : Bool) (word : Word) (heap : Heap 4) :=
  Eval (Instruction 4) (entryEnv guard input) (lower (diamond order)) initial 0 (packet word) heap

private theorem runCase (order : Projection) (guard : Bool) (word : Word) (heap : Heap 4)
    (expected : (diamond order).denote guard input initial = (word, heap)) :
    targetReturns order guard word heap :=
  (returns_iff (diamond order) guard input initial word heap).mp
    (((diamond order).returns_iff_denote guard input initial word heap).mpr expected)

example : targetReturns .onTrue true 11 afterTrue := runCase .onTrue true 11 afterTrue (by cbv)
example : targetReturns .onTrue false 33 afterFalse := runCase .onTrue false 33 afterFalse (by cbv)
example : targetReturns .onFalse true 11 afterTrue := runCase .onFalse true 11 afterTrue (by cbv)
example : targetReturns .onFalse false 33 afterFalse := runCase .onFalse false 33 afterFalse (by cbv)

-- The returned word alone is insufficient. A write by the untaken arm
-- would be observable at its distinct save cell.
example : ¬ targetReturns .onFalse true 11 (afterTrue.write falseCell 7) := by
  intro run
  have heap := ((lower_eval_iff (diamond .onFalse) true input initial (afterTrue.write falseCell 7)
    0 (packet 11)).mp run).2.2
  have atCell := congrFun heap falseCell
  have untouched : ((diamond .onFalse).denote true input initial).2 falseCell = 0 := by cbv
  have impossible : (7 : Word) = 0 := by
    simpa only [Heap.write, Function.update_self, untouched] using atCell
  exact (by decide : (7 : Word) ≠ 0) impossible

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA
