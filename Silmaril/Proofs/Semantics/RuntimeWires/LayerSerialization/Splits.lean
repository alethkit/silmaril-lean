module

public import Silmaril.Semantics.RuntimeWires.LayerSerialization.Defs
import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.LayerSerialization

open Silmaril.RuntimeWires.ProgressiveGraph
open Silmaril.RuntimeWires.ProgressiveGraph.Diagram
open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable (d : ProgressiveGraph.Diagram S V W kind)

private theorem vertexStep_split (j : Fin V) (a b c : Bool)
    (hab : a = true → b = true) (hbc : b = true → c = true)
    {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (h : Row.Split S r p q) :
    Row.Split S (d.vertexStep j a c (hbc ∘ hab) r)
      (d.vertexStep j a b hab p) (d.vertexStep j b c hbc q) := by
  cases a <;> cases b <;> cases c
  · exact h.pass _
  · exact .lower _ h
  · exact Bool.noConfusion (hbc rfl)
  · exact .upper _ h
  · exact Bool.noConfusion (hab rfl)
  · exact Bool.noConfusion (hab rfl)
  · exact Bool.noConfusion (hbc rfl)
  · exact h.pass _

theorem layerStep_split {a b c : Finset (Fin V)} (hab : a ⊆ b) (hbc : b ⊆ c)
    (slots : List (LayerSlot V W)) :
    Row.Split S (d.layerStep (hab.trans hbc) slots) (d.layerStep hab slots)
      (d.layerStep hbc slots) := by
  induction slots with
  | nil => exact .empty
  | cons slot slots ih =>
    cases slot with
    | inl w => exact .wire (d.label w) ih
    | inr j => exact vertexStep_split d j _ _ _ _ _ ih

private theorem vertexStep_same (j : Fin V) (a : Bool) (A : List O) :
    d.vertexStep j a a id (Row.straight A) = Row.straight (d.vertexWord j a ++ A) := by
  cases a <;> exact Row.pass_straight _ _

private theorem layerStep_same (a : Finset (Fin V)) (slots : List (LayerSlot V W)) :
    d.layerStep (Finset.Subset.refl a) slots = Row.straight (d.frontier a slots) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot with
    | inl w =>
      change Row.wire (d.label w) (d.layerStep _ slots) = Row.wire (d.label w) _
      rw [ih]
    | inr j =>
      change d.vertexStep j _ _ _ (d.layerStep _ slots) = Row.straight _
      rw [ih]
      exact vertexStep_same d j _ _

theorem mem_completed (done : Finset (Fin V)) (order : List (Fin V)) (j : Fin V) :
    j ∈ completed done order ↔ j ∈ done ∨ j ∈ order := by
  induction order generalizing done with
  | nil => simp [completed]
  | cons i tail ih =>
    change j ∈ completed (insert i done) tail ↔ _
    rw [ih, Finset.mem_insert, List.mem_cons]
    simp only [or_assoc, or_left_comm]

theorem subset_completed (done : Finset (Fin V)) (order : List (Fin V)) :
    done ⊆ completed done order :=
  fun j h => (mem_completed done order j).mpr (Or.inl h)

/-- Merge the serial steps using the actual splits of the residual layer
row. The empty schedule leaves only a removable straight row. -/
theorem serializeFrom_seam (slots : List (LayerSlot V W)) (done : Finset (Fin V))
    (order : List (Fin V)) :
    Sheet.SeamEquivalent (d.serializeFrom slots done order)
      (.cons (d.layerStep (subset_completed done order) slots) (.empty _)) := by
  induction order generalizing done with
  | nil =>
    change Sheet.SeamEquivalent (.empty _) (.cons (d.layerStep (Finset.Subset.refl done) slots) _)
    rw [layerStep_same]
    exact .rel _ _ (.straight _)
  | cons j tail ih =>
    let h := Finset.subset_insert j done
    let k := subset_completed (insert j done) tail
    have split := layerStep_split d h k slots
    exact .trans _ _ _ ((ih (insert j done)).cons (d.layerStep h slots))
      (.symm _ _ (.rel _ _ (.split split (.empty _))))

theorem frontier_empty (slots : List (LayerSlot V W)) :
    d.frontier ∅ slots = slots.flatMap d.slotSource := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    cases slot <;> simp [Diagram.frontier, Diagram.slotSource, Diagram.vertexWord, ih]

theorem frontier_full (slots : List (LayerSlot V W)) (done : Finset (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ done) :
    d.frontier done slots = slots.flatMap d.slotTarget := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    have rest := ih (fun j hj => covers j (.tail _ hj))
    cases slot with
    | inl w => simp [Diagram.frontier, Diagram.slotTarget, rest]
    | inr j =>
      have here := covers j (.head _)
      simp [Diagram.frontier, Diagram.slotTarget, Diagram.vertexWord, here, rest]

private theorem wire_heq {A B X Y : List O} {r : Row S A B} {q : Row S X Y}
    (a : A = X) (b : B = Y) (h : HEq r q) (x : O) : HEq (Row.wire x r) (Row.wire x q) := by
  subst a
  subst b
  cases eq_of_heq h
  rfl

private theorem full_vertex_heq {A B X Y : List O} {r : Row S A B} {q : Row S X Y}
    (a : A = X) (b : B = Y) (h : HEq r q) (j : Fin V) (i k : Bool)
    (hi : i = false) (hk : k = true) (mono : i = true → k = true) :
    HEq (d.vertexStep j i k mono r) (Row.box (d.generator j) q) := by
  subst a
  subst b
  subst i
  subst k
  cases eq_of_heq h
  rfl

private theorem layerStep_full_heq (slots : List (LayerSlot V W)) (done : Finset (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ done) :
    HEq (d.layerStep (Finset.empty_subset done) slots) (d.layerRow slots) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    have rest j (hj : Sum.inr j ∈ slots) := covers j (.tail _ hj)
    have a := frontier_empty d slots
    have b := frontier_full d slots done rest
    cases slot with
    | inl w => exact wire_heq a b (ih rest) (d.label w)
    | inr j =>
      have here := covers j (.head _)
      exact full_vertex_heq d a b (ih rest) j _ _ (by simp) (decide_eq_true here) _

private theorem reindex_heq {A B X Y : List O} (a : A = X) (b : B = Y)
    {r : Row S A B} {q : Row S X Y} (h : HEq r q) : r.reindex a b = q := by
  subst a
  subst b
  exact eq_of_heq h

private theorem layerStep_full (slots : List (LayerSlot V W)) (done : Finset (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ done) :
    (d.layerStep (Finset.empty_subset done) slots).reindex (frontier_empty d slots)
      (frontier_full d slots done covers) = d.layerRow slots :=
  reindex_heq _ _ (layerStep_full_heq d slots done covers)

theorem serializeFrom_full (slots : List (LayerSlot V W)) (order : List (Fin V))
    (covers : ∀ j, Sum.inr j ∈ slots → j ∈ completed ∅ order) :
    Sheet.SeamEquivalent
      ((d.serializeFrom slots ∅ order).reindex (frontier_empty d slots)
        (frontier_full d slots (completed ∅ order) covers))
      (.cons (d.layerRow slots) (.empty _)) := by
  have seam := (serializeFrom_seam d slots ∅ order).reindex
    (frontier_empty d slots) (frontier_full d slots (completed ∅ order) covers)
  rw [Sheet.reindex_single, layerStep_full d slots (completed ∅ order) covers] at seam
  exact seam

end Silmaril.RuntimeWires.Proofs.LayerSerialization
