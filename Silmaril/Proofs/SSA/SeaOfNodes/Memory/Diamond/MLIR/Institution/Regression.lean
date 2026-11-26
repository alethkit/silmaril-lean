module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Backends.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountFixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Model → NativeModel, Equation → NativeEquation
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.Arith (Env)
open Isotope.Institution.Observational (ssaBeh)
open RVSDG (Origin Port)

private def sig : EntrySignature := ⟨[.address, .address, .word]⟩

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

private def sameEffect : NativeEquation sig :=
  ⟨diamond .onFalse store, diamond .onTrue store⟩

private def removeStore : NativeEquation sig :=
  ⟨diamond .onFalse store, diamond .onTrue pass⟩

private def input : Valuation sig :=
  .cons firstCell (.cons secondCell (.cons (17 : Word) .nil))

private def initial : Heap 2 := fun _ => 0
private def firstWritten : Heap 2 := initial.write firstCell 17
private def secondWritten : Heap 2 := initial.write secondCell 17

-- True enters different source predecessor occurrences on the two sides.
example : (sameEffect.lhs.merge.slot .onTrue = .second) ∧ (sameEffect.rhs.merge.slot .onTrue = .first) :=
  ⟨rfl, rfl⟩

example : (room sig).Sat (Discrete.mk input) (translateEquation sameEffect) :=
  (translated_satisfaction sameEffect input).2 (fun _ _ => rfl)

-- The same return word is carried through the three emitted paths.
example : (emit removeStore.lhs).observe input true initial = some (encodeResult 17 firstWritten) := rfl

example : (emit (removeStore.map swap).lhs).observe input true initial =
    some (encodeResult 17 secondWritten) := rfl

example : (emit (removeStore.map swap).rhs).observe input true initial =
    some (encodeResult 17 initial) := rfl

example : (emit (removeStore.map swap).lhs).observe input false initial =
    (emit (removeStore.map swap).rhs).observe input false initial := rfl

private theorem swapped_fails :
    ¬ (room sig).Sat (Discrete.mk input) (translateEquation (removeStore.map swap)) := by
  intro holds
  have equal := Option.some.inj (holds true initial)
  have atCell := congrArg (fun result : Env resultTypes => result.get (.there (.there .here))) equal
  change (17 : Word) = 0 at atCell
  exact (by decide : (17 : Word) ≠ 0) atCell

example : ¬ (room sig).Sat (Discrete.mk (pullback swap input)) (translateEquation removeStore) :=
  fun holds => swapped_fails ((satisfaction_reindex swap removeStore input).2 holds)

example : (Diamond.Institution.ToRVSDG.Program.ofGraph (removeStore.map swap).lhs).observe
      (nativeModel input) true initial = Memory.encodeResult 17 secondWritten :=
  (observe_iff_rvsdg (removeStore.map swap).lhs input true initial 17 secondWritten).1 rfl

example : LambdaSSA.Institution.returnObservation initial (17, secondWritten) ∈
    ssaBeh 1 (LambdaSSA.Institution.entryModel (nativeModel input) true)
      (LambdaSSA.Institution.scope (removeStore.map swap).lhs) :=
  (observe_iff_lambdaSSA (removeStore.map swap).lhs input true initial 17 secondWritten).1 rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountRegression

open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Model → NativeModel, Equation → NativeEquation
open RVSDG (Port Tuple)

open CellCountFixture (commuteSwaps threeInputs threeHeap)
open CellCountFixture renaming sig → swapSignature

private theorem address_cases (address : Address 2) : address = firstCell ∨ address = secondCell :=
  Fin.cases (.inl rfl) (fun i => .inr (congrArg Fin.succ (Fin.eq_zero i))) address

private def swapHeap (heap : Heap 2) (x y : Address 2) : Heap 2 :=
  (heap.write x (heap y)).write y (heap x)

private theorem swaps_agree_on_two_cells (x y z : Address 2) (word : Word) (heap : Heap 2)
    (guard : Bool) :
    let values : Valuation swapSignature := .cons x (.cons y (.cons z (.cons word .nil)))
    commuteSwaps.lhs.denote guard values heap = commuteSwaps.rhs.denote guard values heap := by
  change (word, swapHeap (swapHeap heap x y) y z) = (word, swapHeap (swapHeap heap y z) x y)
  apply congrArg (Prod.mk word)
  funext observed
  rcases address_cases x with rfl | rfl <;>
    rcases address_cases y with rfl | rfl <;>
    rcases address_cases z with rfl | rfl <;>
    rcases address_cases observed with rfl | rfl <;> rfl

-- On two cells every addressed swap is the identity or the same transposition.
private theorem validAtTwoCells : HoldsTwoCells commuteSwaps := by
  intro values guard heap
  cases values with
  | cons x values =>
    cases values with
    | cons y values =>
      cases values with
      | cons z values =>
        cases values with
        | cons word rest =>
          cases rest
          exact swaps_agree_on_two_cells x y z word heap guard

example : ∀ input, (room swapSignature).Sat (CategoryTheory.Discrete.mk input) (translateEquation commuteSwaps) :=
  (validity_two_cells commuteSwaps).2 validAtTwoCells

-- With three distinct addresses the two orders produce different rotations.
example : ¬ ∀ model : NativeModel swapSignature, commuteSwaps.Holds model := by
  intro valid
  have equal := valid ⟨3, threeInputs⟩ true threeHeap
  have atCell := congrArg (fun result : Word × Heap 3 => result.2 (0 : Address 3)) equal
  change (1 : Word) = 2 at atCell
  exact (by decide : (1 : Word) ≠ 2) atCell

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.CellCountRegression
