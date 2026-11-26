module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution

open CategoryTheory
open RVSDG (Origin)
open SeaOfNodes.Diamond (Projection)

private def sig : Signature := ⟨[.address, .address, .word]⟩

private def swap : sig ⟶ sig :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail .head) => .tail (.tail .head)⟩

private def word : Origin sig.args [] .word := .arg (.tail (.tail .head))

private def passArm : Memory.Graph sig.args :=
  .ret (.latest 0) word

private def writeArm : Memory.Graph sig.args :=
  .store (.latest 0) (.arg .head) word (.ret (.latest 1) word)

private def diamond (first : Projection) (trueArm : Memory.Graph sig.args) : Graph sig.args where
  merge := ⟨first⟩
  arm
    | .onTrue => trueArm
    | .onFalse => passArm
  suffix := .ret (.latest 0) (.arg .head)

private def sameEffect : Equation sig :=
  ⟨diamond .onFalse writeArm, diamond .onTrue writeArm⟩

private def removeStore : Equation sig :=
  ⟨diamond .onFalse writeArm, diamond .onTrue passArm⟩

private def firstCell : Address 2 := 0
private def secondCell : Address 2 := 1

private def model : Model sig :=
  ⟨2, .cons firstCell (.cons secondCell (.cons (17 : Word) .nil))⟩

private def initial : Heap model.cells := fun _ => 0

private def final : Heap model.cells := initial.write secondCell 17

-- Predecessor order can change while the complete observation agrees.
example (m : Model sig) : sameEffect.Holds m := by
  intro guard heap
  rfl

example : (room sig).Sat (Discrete.mk model) (sameEffect.map swap) :=
  ((corridor swap).sat (Discrete.mk model) sameEffect).2 (fun _ _ => rfl)

-- Both sides of the second equation return the same word, even after renaming.
example (m : Model sig) (guard : Bool) (heap : Heap m.cells) :
    (m.observe (removeStore.map swap).lhs guard heap).1 =
      (m.observe (removeStore.map swap).rhs guard heap).1 := by
  cases guard <;> rfl

-- The typed swap moves the taken store from cell 0 to cell 1. The true arm
-- still enters at the second occurrence.
example : (mapGraph swap removeStore.lhs).merge.slot .onTrue = .second := rfl

example : (mapGraph swap removeStore.lhs).Returns true model.input initial 17 final :=
  (model.returns_iff_observe _ true initial 17 final).2 (by cbv)

example : (model.observe removeStore.lhs true initial).2 secondCell = 0 := by cbv
example : (model.observe (removeStore.map swap).lhs true initial).2 firstCell = 0 := by cbv

private theorem translated_not_holds : ¬ (room sig).Sat (Discrete.mk model) (removeStore.map swap) := by
  intro holds
  have equalAtCell := congrArg (fun (result : Word × Heap model.cells) => result.2 secondCell)
    (holds true initial)
  have written : (model.observe (removeStore.map swap).lhs true initial).2 secondCell = 17 := by cbv
  have untouched : (model.observe (removeStore.map swap).rhs true initial).2 secondCell = 0 := by cbv
  exact (by decide : (17 : Word) ≠ 0) (written.symm.trans (equalAtCell.trans untouched))

example : ¬ removeStore.Holds (reduct swap model) :=
  fun holds => translated_not_holds ((removeStore.satisfaction swap model).2 holds)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution
