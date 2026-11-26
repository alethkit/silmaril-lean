module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG

open CategoryTheory
open SeaOfNodes.Diamond (Projection)
open RVSDG (Origin Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)

private def sig : Signature := ⟨[.address, .address, .word]⟩

private def swap : sig ⟶ sig :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail .head) => .tail (.tail .head)⟩

private def word : Origin sig.args [] .word := .arg (.tail (.tail .head))

private def pass : Memory.Graph sig.args := .ret (.latest 0) word

private def store : Memory.Graph sig.args :=
  .store (.latest 0) (.arg .head) word (.ret (.latest 1) word)

private def diamond (first : Projection) (arm : Memory.Graph sig.args) : Graph sig.args :=
  ⟨⟨first⟩, fun | .onTrue => arm | .onFalse => pass, .ret (.latest 0) (.arg .head)⟩

private def sameEffect : Equation sig :=
  ⟨diamond .onFalse store, diamond .onTrue store⟩

private def removeStore : Equation sig :=
  ⟨diamond .onFalse store, diamond .onTrue pass⟩

private def firstCell : Address 2 := 0
private def secondCell : Address 2 := 1

private def model : Model sig :=
  ⟨2, .cons firstCell (.cons secondCell (.cons (17 : Word) .nil))⟩

private def initial : Heap model.cells := fun _ => 0

-- The left and right encodings put true at different numbered predecessors.
example :
    ((sameEffect.lhs.encodeEntry true model.input initial).get .head).down = 1 ∧
      ((sameEffect.rhs.encodeEntry true model.input initial).get .head).down = 0 :=
  ⟨rfl, rfl⟩

example : (room sig).Sat (Discrete.mk model) (translateEquation sameEffect) :=
  (translated_satisfaction sameEffect model).2 (fun _ _ => rfl)

-- Sharing the same numbered selector compares different source guards.
example : ¬ (RVSDG.Institution.room.{0, 0, 0} targetSignature).Sat
    (Discrete.mk (leafModel 2).toRVSDG) (translateEquation sameEffect).sharedInputEquation := by
  intro holds
  have equal := holds (sameEffect.lhs.encodeEntry false model.input initial)
  have atCell := congrArg (fun out : Tuple (WireVal 2) (Threaded wordPorts) =>
    out.get (.tail .head) firstCell) equal
  change (0 : Word) = 17 at atCell
  exact (by decide : (0 : Word) ≠ 17) atCell

-- The actual numbered evaluator returns the same word in each case.
-- Swapping the two address ports moves the taken store to the second cell.
example : (translateEquation removeStore).lhs.observe model true initial =
    encodeResult 17 (initial.write firstCell 17) := rfl

example : (translateEquation (removeStore.map swap)).lhs.observe model true initial =
    encodeResult 17 (initial.write secondCell 17) := rfl

example : (translateEquation (removeStore.map swap)).rhs.observe model true initial =
    encodeResult 17 initial := rfl

example : (translateEquation (removeStore.map swap)).lhs.observe model false initial =
    (translateEquation (removeStore.map swap)).rhs.observe model false initial := rfl

private theorem swapped_fails :
    ¬ (room sig).Sat (Discrete.mk model) (translateEquation (removeStore.map swap)) := by
  intro holds
  have atCell := congrArg (fun out : Tuple (WireVal 2) (Threaded wordPorts) =>
    out.get (.tail .head) secondCell) (holds true initial)
  change (17 : Word) = 0 at atCell
  exact (by decide : (17 : Word) ≠ 0) atCell

example : ¬ (room sig).Sat (Discrete.mk (reduct swap model)) (translateEquation removeStore) :=
  fun holds => swapped_fails ((room_satisfaction_reindex swap removeStore model).2 holds)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG
