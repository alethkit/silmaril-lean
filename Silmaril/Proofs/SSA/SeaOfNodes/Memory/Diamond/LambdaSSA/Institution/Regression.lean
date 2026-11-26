module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Thms

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → NativeSignature, Model → NativeModel, Equation → NativeEquation
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution (mapGraph reduct)
open SeaOfNodes.Diamond (Projection)
open RVSDG (Origin)
open Isotope.Institution.Observational (ssaBeh)

private def sig : NativeSignature := ⟨[.address, .address, .word]⟩

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

private def removeStore : NativeEquation sig :=
  ⟨diamond .onFalse store, diamond .onTrue pass⟩

private def firstCell : Address 2 := 0
private def secondCell : Address 2 := 1

private def model : NativeModel sig :=
  ⟨2, .cons firstCell (.cons secondCell (.cons (17 : Word) .nil))⟩

private def initial : Heap model.cells := fun _ => 0
private def firstWritten : Heap model.cells := initial.write firstCell 17
private def secondWritten : Heap model.cells := initial.write secondCell 17

private abbrev behaviors (graph : Graph sig.args) :=
  ssaBeh 1 (entryModel model true) (scope graph)

private theorem observed (graph : Graph sig.args) (final : Heap model.cells)
    (pair : model.observe graph true initial = (17, final)) :
    returnObservation initial (17, final) ∈ behaviors graph :=
  (ret_mem_returns graph model true initial 17 final).2
    ((model.returns_iff_observe graph true initial 17 final).2 pair)

-- The original store, swapped store, and omitted store all return the same
-- packet. Their whole final heaps differ.
example : returnObservation initial (17, firstWritten) ∈ behaviors removeStore.lhs :=
  observed _ _ (by cbv)

example : returnObservation initial (17, secondWritten) ∈ behaviors (removeStore.map swap).lhs :=
  observed _ _ (by cbv)

example : returnObservation initial (17, initial) ∈ behaviors (removeStore.map swap).rhs :=
  observed _ _ (by cbv)

-- Both incoming jumps still target the join. The true jump is the second
-- predecessor occurrence after changing the address wires.
example : (edge (mapGraph swap removeStore.lhs) .first).source = .onFalse ∧
    (edge (mapGraph swap removeStore.lhs) .second).source = .onTrue := ⟨rfl, rfl⟩

example :
    (room sig).Sat (Discrete.mk (entryModel model false)) (translateEquation (removeStore.map swap)) :=
  (room_satisfaction_at (removeStore.map swap) model false).2 (fun _ => rfl)

private theorem true_guard_fails :
    ¬ (room sig).Sat (Discrete.mk (entryModel model true)) (translateEquation (removeStore.map swap)) := by
  intro sat
  have pair := (room_satisfaction_at (removeStore.map swap) model true).1 sat initial
  have equal := congrArg (fun result : Word × Heap model.cells => result.2 secondCell) pair
  have written : (model.observe (removeStore.map swap).lhs true initial).2 secondCell = 17 := by cbv
  have untouched : (model.observe (removeStore.map swap).rhs true initial).2 secondCell = 0 := by cbv
  exact (by decide : (17 : Word) ≠ 0) (written.symm.trans (equal.trans untouched))

example : ¬ (room sig).Sat (Discrete.mk (entryModel (reduct swap model) true))
    (translateEquation removeStore) :=
  fun sat => true_guard_fails ((room_satisfaction_reindex swap removeStore model true).2 sat)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution
