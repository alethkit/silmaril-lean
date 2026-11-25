module

public import Silmaril.Semantics.RuntimeWires.NullaryGaps.Defs
import Silmaril.Semantics.RuntimeWires.SeamPlacement.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.NullaryGaps

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem row_count_zero {A B : List O} (r : Row S A B) :
    (r.labelsInGap 0).length = r.boxesBeforeFirstWire := by
  induction r with
  | empty | wire => rfl
  | box e r ih => simp only [Row.labelsInGap, Row.boxesBeforeFirstWire, List.length_cons, ih]

theorem sheet_count_zero {A B : List O} (p : Sheet S A B) :
    (p.labelsInGap 0).length = p.boxesBeforeFirstWire := by
  induction p with
  | empty => rfl
  | cons r p ih => simp only [Sheet.labelsInGap, Sheet.boxesBeforeFirstWire, List.length_append, row_count_zero, ih]

private theorem pass_empty {word A B : List O} (r : Row S A B) (nil : word = []) (gap : ℕ) :
    (Row.pass word r).labelsInGap gap = r.labelsInGap gap := by
  subst word
  rfl

theorem split_labels {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (split : Row.Split S r p q) (nullary : ∀ e, S.source e = [] ∧ S.target e = []) (gap : ℕ) :
    (r.labelsInGap gap).Perm (p.labelsInGap gap ++ q.labelsInGap gap) := by
  induction split generalizing gap with
  | empty => exact .nil
  | wire x _ ih =>
    cases gap
    · exact .nil
    · exact ih _
  | upper e _ ih =>
    rw [pass_empty _ (nullary e).2]
    cases gap
    · exact (ih 0).cons e
    · exact ih _
  | lower e _ ih =>
    rw [pass_empty _ (nullary e).1]
    cases gap
    · exact ((ih 0).cons e).trans List.perm_middle.symm
    · exact ih _

theorem straight_labels (word : List O) (gap : ℕ) :
    (Row.straight (S := S) word).labelsInGap gap = [] := by
  induction word generalizing gap with
  | nil => rfl
  | cons x word ih =>
    cases gap
    · rfl
    · exact ih _

private theorem move_labels {A B : List O} {p q : Sheet S A B} (move : Sheet.Move S p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) (gap : ℕ) :
    (p.labelsInGap gap).Perm (q.labelsInGap gap) := by
  induction move with
  | split split tail =>
    simpa only [Sheet.labelsInGap, List.append_assoc] using
      (split_labels split nullary gap).append_right (tail.labelsInGap gap)
  | straight tail =>
    simp only [Sheet.labelsInGap, straight_labels, List.nil_append, List.Perm.refl]
  | under row _ ih =>
    exact ih.append_left _

theorem seam_labels {A B : List O} {p q : Sheet S A B} (same : Sheet.SeamEquivalent p q)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) (gap : ℕ) :
    (p.labelsInGap gap).Perm (q.labelsInGap gap) := by
  induction same with
  | rel _ _ h => exact move_labels h nullary gap
  | refl => exact .refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ i j => exact i.trans j

private theorem row_labels_beyond {A B : List O} (r : Row S A B)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) {gap : ℕ} (outside : A.length < gap) :
    r.labelsInGap gap = [] := by
  induction r generalizing gap with
  | empty => rfl
  | wire x r ih =>
    cases gap with
    | zero => rfl
    | succ k =>
      exact ih (by simpa using outside)
  | box e r ih =>
    cases gap with
    | zero => simp at outside
    | succ k =>
      apply ih
      simpa only [(nullary e).1, List.nil_append] using outside

theorem labels_beyond {A B : List O} (p : Sheet S A B)
    (nullary : ∀ e, S.source e = [] ∧ S.target e = []) {gap : ℕ} (outside : A.length < gap) :
    p.labelsInGap gap = [] := by
  induction p with
  | empty => rfl
  | cons row rest ih =>
    have same := row.boundary_eq_of_nullary nullary
    simp only [Sheet.labelsInGap, row_labels_beyond row nullary outside, ih (same ▸ outside),
      List.nil_append]

end Silmaril.RuntimeWires.Proofs.NullaryGaps
