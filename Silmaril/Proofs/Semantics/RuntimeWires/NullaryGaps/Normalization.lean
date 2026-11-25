module

public import Silmaril.Semantics.RuntimeWires.NullaryGaps.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.NullaryGaps.Soundness
import Silmaril.Semantics.RuntimeWires.SeamPlacement.Thms
import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
import Mathlib.Data.Multiset.Basic

public section

namespace Silmaril.RuntimeWires.Proofs.NullaryGaps

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {E : Type v}

private abbrev scalarSignature (O : Type u) (E : Type v) : Signature.{u,v} O where
  Edge := E
  source _ := []
  target _ := []

local notation "C" => scalarSignature O E

private def prependBoxes {A B : List O} (labels : List E) (r : Row C A B) : Row C A B :=
  match labels with
  | [] => r
  | e :: rest => .box e (prependBoxes rest r)

private def render (word : List O) (labels : ℕ → List E) : Row C word word :=
  match word with
  | [] => prependBoxes (labels 0) .empty
  | x :: rest => prependBoxes (labels 0) (.wire x (render rest (labels ∘ Nat.succ)))

private abbrev single {A : List O} (r : Row C A A) : Sheet C A A :=
  .cons r (.empty _)

private theorem render_empty (word : List O) :
    render (E := E) word (fun _ => []) = Row.straight word := by
  induction word with
  | nil => rfl
  | cons x word ih =>
    exact congrArg (Row.wire x) ih

private theorem render_box (word : List O) (e : E) (labels : ℕ → List E) :
    render word (fun i => match i with
      | 0 => e :: labels 0
      | n + 1 => labels (n + 1)) = Row.box e (render word labels) := by
  cases word <;> rfl

private theorem row_rebuild {A B : List O} (r : Row C A B) :
    HEq (render A r.labelsInGap) r := by
  induction r with
  | empty => rfl
  | @wire x A B r ih =>
    have same := r.boundary_eq_of_nullary (fun _ => ⟨rfl, rfl⟩)
    subst B
    exact congrArg (Row.wire x) (eq_of_heq ih) |>.heq
  | @box e A B r ih =>
    have same := r.boundary_eq_of_nullary (fun _ => ⟨rfl, rfl⟩)
    subst B
    have read : (Row.box (S := C) e r).labelsInGap = (fun i => match i with
      | 0 => e :: r.labelsInGap 0
      | n + 1 => r.labelsInGap (n + 1)) := by
      funext i
      cases i <;> rfl
    have eq := render_box A e r.labelsInGap
    change HEq (render A (Row.box (S := C) e r).labelsInGap) (Row.box e r)
    rw [read]
    exact (eq.trans (congrArg (Row.box e) (eq_of_heq ih))).heq

private theorem prepend_split {A M B : List O} {r : Row C A B} {p : Row C A M} {q : Row C M B}
    (h : Row.Split C r p q) (upper lower : List E) :
    Row.Split C (prependBoxes (upper ++ lower) r) (prependBoxes upper p) (prependBoxes lower q) := by
  induction upper with
  | nil =>
    induction lower with
    | nil => exact h
    | cons e lower ih => exact .lower e ih
  | cons e upper ih => exact .upper e ih

private theorem render_split (word : List O) (upper lower : ℕ → List E) :
    Row.Split C (render word (fun i => upper i ++ lower i)) (render word upper) (render word lower) := by
  induction word generalizing upper lower with
  | nil => exact prepend_split .empty (upper 0) (lower 0)
  | cons x word ih =>
    exact prepend_split (.wire x (ih (upper ∘ Nat.succ) (lower ∘ Nat.succ))) (upper 0) (lower 0)

/-- Combining the rows concatenates the label lists independently in
each gap. A straight row handles the empty sheet. -/
private theorem normalize {A B : List O} (p : Sheet C A B) :
    ∃ h : A = B, Sheet.SeamEquivalent p ((single (render A p.labelsInGap)).reindex rfl h) := by
  induction p with
  | empty word =>
    refine ⟨rfl, ?_⟩
    change Sheet.SeamEquivalent (.empty word) (single (render (E := E) word (fun _ => [])))
    rw [render_empty]
    exact .rel _ _ (.straight _)
  | @cons A M B r rest ih =>
    have same := r.boundary_eq_of_nullary (fun _ => ⟨rfl, rfl⟩)
    subst M
    obtain ⟨h, tail⟩ := ih
    subst B
    refine ⟨rfl, ?_⟩
    have together := render_split A r.labelsInGap rest.labelsInGap
    rw [eq_of_heq (row_rebuild r)] at together
    change Sheet.SeamEquivalent (.cons r rest)
      (single (render A (fun i => r.labelsInGap i ++ rest.labelsInGap i)))
    exact .trans _ _ _ (Sheet.SeamEquivalent.cons r tail)
      (.symm _ _ (.rel _ _ (.split together (.empty _))))

private theorem prepend_schedule {A : List O} (labels : List E) (r : Row C A A) :
    Sheet.SeamEquivalent (single (prependBoxes labels r))
      (.cons (prependBoxes labels (Row.straight A)) (single r)) := by
  have h := prepend_split (Row.Split.all_lower r) labels []
  rw [List.append_nil] at h
  exact .rel _ _ (.split h (.empty A))

private theorem prepend_congr {A : List O} (labels : List E) {r s : Row C A A}
    (h : Sheet.SeamEquivalent (single r) (single s)) :
    Sheet.SeamEquivalent (single (prependBoxes labels r)) (single (prependBoxes labels s)) :=
  .trans _ _ _ (prepend_schedule labels r)
    (.trans _ _ _ (h.cons _) (.symm _ _ (prepend_schedule labels s)))

/-- Put the first label above the seam and the second below it, from
either horizontal order. The remainder is all below the seam. -/
private theorem adjacent_exchange {A : List O} (e f : E) (r : Row C A A) :
    Sheet.SeamEquivalent (single (.box e (.box f r))) (single (.box f (.box e r))) := by
  let above : Row C A A := .box e (.straight A)
  let below : Row C A A := .box f r
  have first : Row.Split C (.box e (.box f r)) above below :=
    .upper e (.lower f (Row.Split.all_lower r))
  have second : Row.Split C (.box f (.box e r)) above below :=
    .lower f (.upper e (Row.Split.all_lower r))
  exact .trans _ _ _ (.rel _ _ (.split first (.empty A)))
    (.symm _ _ (.rel _ _ (.split second (.empty A))))

private theorem prepend_perm {A : List O} {a b : List E} (perm : a.Perm b) (r : Row C A A) :
    Sheet.SeamEquivalent (single (prependBoxes a r)) (single (prependBoxes b r)) := by
  induction perm with
  | nil => exact .refl _
  | cons e _ ih => exact prepend_congr [e] ih
  | swap e f tail => exact adjacent_exchange f e (prependBoxes tail r)
  | trans _ _ first last => exact .trans _ _ _ first last

private theorem render_perm (word : List O) {a b : ℕ → List E}
    (perm : ∀ i, (a i).Perm (b i)) :
    Sheet.SeamEquivalent (single (render word a)) (single (render word b)) := by
  induction word generalizing a b with
  | nil => exact prepend_perm (perm 0) .empty
  | cons x word ih =>
    have tail := ih (fun i => perm (i + 1))
    have left := prepend_perm (perm 0) (Row.wire x (render word (a ∘ Nat.succ)))
    exact .trans _ _ _ left (prepend_congr (b 0) (tail.padLeft [x]))

private theorem complete_scalar {A : List O} {p q : Sheet C A A}
    (perm : ∀ i, (p.labelsInGap i).Perm (q.labelsInGap i)) : Sheet.SeamEquivalent p q := by
  obtain ⟨_, hp⟩ := normalize p
  obtain ⟨_, hq⟩ := normalize q
  exact .trans _ _ _ hp (.trans _ _ _ (render_perm A perm) (.symm _ _ hq))

theorem complete {S : Signature.{u,v} O} {A : List O} {p q : Sheet S A A}
    (nullary : ∀ e, S.source e = [] ∧ S.target e = [])
    (perm : ∀ i, (p.labelsInGap i).Perm (q.labelsInGap i)) : Sheet.SeamEquivalent p q := by
  cases S with
  | mk E source target =>
    have sourceEmpty : source = fun _ : E => [] := funext (fun e => (nullary e).1)
    have targetEmpty : target = fun _ : E => [] := funext (fun e => (nullary e).2)
    subst source
    subst target
    exact complete_scalar perm

theorem classify {S : Signature.{u,v} O} {A : List O} {p q : Sheet S A A}
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) :
    Sheet.SeamEquivalent p q ↔ p.gapMultisets = q.gapMultisets := by
  constructor
  · intro same
    funext gap
    exact Multiset.coe_eq_coe.mpr (seam_labels same nullary gap.val)
  · intro equal
    apply complete nullary
    intro gap
    by_cases inRange : gap < A.length + 1
    · exact Multiset.coe_eq_coe.mp (congrFun equal ⟨gap, inRange⟩)
    · have outside : A.length < gap := by omega
      rw [labels_beyond p nullary outside, labels_beyond q nullary outside]

private theorem prepend_labels_zero {A B : List O} (labels : List E) (r : Row C A B) :
    (prependBoxes labels r).labelsInGap 0 = labels ++ r.labelsInGap 0 := by
  induction labels with
  | nil => rfl
  | cons e labels ih => exact congrArg (e :: ·) ih

private theorem prepend_labels_succ {A B : List O} (labels : List E) (r : Row C A B) (gap : ℕ) :
    (prependBoxes labels r).labelsInGap (gap + 1) = r.labelsInGap (gap + 1) := by
  induction labels with
  | nil => rfl
  | cons e labels ih => exact ih

private theorem render_labels (word : List O) (labels : ℕ → List E) {gap : ℕ}
    (within : gap < word.length + 1) : (render word labels).labelsInGap gap = labels gap := by
  induction word generalizing labels gap with
  | nil =>
    have zero : gap = 0 := by simpa using within
    subst gap
    simp only [render, prepend_labels_zero, Row.labelsInGap, List.append_nil]
  | cons x word ih =>
    cases gap with
    | zero => simp only [render, prepend_labels_zero, Row.labelsInGap, List.append_nil]
    | succ gap =>
      simp only [render, prepend_labels_succ, Row.labelsInGap]
      exact ih (labels ∘ Nat.succ) (by simpa using within)

theorem realize {S : Signature.{u,v} O} {A : List O}
    (nullary : ∀ e, S.source e = [] ∧ S.target e = [])
    (desired : Fin (A.length + 1) → Multiset S.Edge) :
    ∃ p : Sheet S A A, p.gapMultisets = desired := by
  cases S with
  | mk E source target =>
    have sourceEmpty : source = fun _ : E => [] := funext (fun e => (nullary e).1)
    have targetEmpty : target = fun _ : E => [] := funext (fun e => (nullary e).2)
    subst source
    subst target
    let labels (gap : ℕ) : List E :=
      if h : gap < A.length + 1 then (desired ⟨gap, h⟩).toList else []
    refine ⟨single (render A labels), funext (fun gap => ?_)⟩
    change (↑((render A labels).labelsInGap gap.val ++ ([] : List E)) : Multiset E) = desired gap
    rw [List.append_nil, render_labels A labels gap.isLt]
    simp only [labels, dite_eq_left gap.isLt, Multiset.coe_toList]

end Silmaril.RuntimeWires.Proofs.NullaryGaps
