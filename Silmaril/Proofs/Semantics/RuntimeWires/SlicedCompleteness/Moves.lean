module

public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Splits

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

private theorem map_equivalence {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (f : α → β) (moves : ∀ {x y}, r x y → s (f x) (f y))
    {x y : α} (h : Relation.EqvGen r x y) : Relation.EqvGen s (f x) (f y) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (moves h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem move_suffix {A B C : List O} {p q : Sheet S A B} (h : Sheet.Move S p q)
    (tail : Sheet S B C) : Sheet.Move S (p.thenDo tail) (q.thenDo tail) := by
  induction h with
  | split h rest => exact .split h (rest.thenDo tail)
  | straight rest => exact .straight (rest.thenDo tail)
  | under r h ih => exact .under r (ih tail)

private theorem move_prefix {A B C : List O} {p q : Sheet S B C} (h : Sheet.Move S p q)
    (head : Sheet S A B) : Sheet.Move S (head.thenDo p) (head.thenDo q) := by
  induction head with
  | empty => exact h
  | cons r rest ih => exact .under r (ih h)

theorem seam_then {A B C : List O} {p p' : Sheet S A B} {q q' : Sheet S B C}
    (h : Sheet.SeamEquivalent p p') (k : Sheet.SeamEquivalent q q') :
    Sheet.SeamEquivalent (p.thenDo q) (p'.thenDo q') :=
  .trans _ _ _ (map_equivalence (·.thenDo q) (fun {_ _} m => move_suffix m q) h)
    (map_equivalence (p'.thenDo ·) (fun {_ _} m => move_prefix m p') k)

theorem seam_cons {A B C : List O} (r : Row S A B) {p q : Sheet S B C}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (.cons r p) (.cons r q) :=
  map_equivalence (Sheet.cons r) (fun {_ _} m => Sheet.Move.under r m) h

private theorem move_padLeft (W : List O) {A B : List O} {p q : Sheet S A B}
    (h : Sheet.Move S p q) : Sheet.Move S (p.padLeft W) (q.padLeft W) := by
  induction h with
  | split h tail => exact .split (split_pass W h) (tail.padLeft W)
  | @straight A B tail =>
    change Sheet.Move S (tail.padLeft W) (.cons (Row.pass W (Row.straight A)) (tail.padLeft W))
    rw [pass_straight]
    exact .straight _
  | under r h ih => exact .under (Row.pass W r) ih

private theorem move_padRight (W : List O) {A B : List O} {p q : Sheet S A B}
    (h : Sheet.Move S p q) : Sheet.Move S (p.padRight W) (q.padRight W) := by
  induction h with
  | split h tail => exact .split (split_beside h (split_straight W)) (tail.padRight W)
  | @straight A B tail =>
    change Sheet.Move S (tail.padRight W)
      (.cons ((Row.straight A).beside (Row.straight W)) (tail.padRight W))
    rw [straight_beside, pass_straight]
    exact .straight _
  | under r h ih => exact .under (r.beside (Row.straight W)) ih

theorem seam_padLeft (W : List O) {A B : List O} {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.padLeft W) (q.padLeft W) :=
  map_equivalence (·.padLeft W) (fun {_ _} m => move_padLeft W m) h

theorem seam_padRight (W : List O) {A B : List O} {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.padRight W) (q.padRight W) :=
  map_equivalence (·.padRight W) (fun {_ _} m => move_padRight W m) h

theorem seam_tensor {A B X Y : List O} {p p' : Sheet S A B} {q q' : Sheet S X Y}
    (h : Sheet.SeamEquivalent p p') (k : Sheet.SeamEquivalent q q') :
    Sheet.SeamEquivalent (p.tensor q) (p'.tensor q') :=
  seam_then (seam_padRight X h) (seam_padLeft B k)

theorem seam_reindex {A B X Y : List O} (a : A = X) (b : B = Y) {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.reindex a b) (q.reindex a b) := by
  subst a
  subst b
  exact h

/-- The two serial schedules of a single horizontal row agree by its two split witnesses. -/
theorem swap_rows {A B X Y Z : List O} (r : Row S A B) (s : Row S X Y)
    (tail : Sheet S (B ++ Y) Z) :
    Sheet.SeamEquivalent
      (.cons (r.beside (Row.straight X)) (.cons (Row.pass B s) tail))
      (.cons (Row.pass A s) (.cons (r.beside (Row.straight Y)) tail)) := by
  have left := split_beside (split_all_upper r) (split_all_lower s)
  have right := split_beside (split_all_lower r) (split_all_upper s)
  rw [straight_beside] at left right
  exact .trans _ (.cons (r.beside s) tail) _
    (.symm _ _ (.rel _ _ (.split left tail))) (.rel _ _ (.split right tail))

theorem swap_row_sheet {A B X Y Z : List O} (r : Row S A B) (q : Sheet S X Y)
    (tail : Sheet S (B ++ Y) Z) :
    Sheet.SeamEquivalent
      (.cons (r.beside (Row.straight X)) ((q.padLeft B).thenDo tail))
      ((q.padLeft A).thenDo (.cons (r.beside (Row.straight Y)) tail)) := by
  induction q with
  | empty => exact .refl _
  | cons s q ih =>
    exact .trans _ _ _ (swap_rows r s ((q.padLeft B).thenDo tail))
      (seam_cons _ (ih tail))

theorem swap_sheets {A B X Y : List O} (p : Sheet S A B) (q : Sheet S X Y) :
    Sheet.SeamEquivalent (p.tensor q) ((q.padLeft A).thenDo (p.padRight Y)) := by
  induction p with
  | empty W =>
    have h : (q.padLeft W).thenDo (.empty (W ++ Y)) = q.padLeft W :=
      sheet_ext (by simp only [seq_cells, sheetCells, List.append_nil])
    change Sheet.SeamEquivalent (q.padLeft W) ((q.padLeft W).thenDo (.empty (W ++ Y)))
    rw [h]
    exact .refl _
  | cons r p ih =>
    exact .trans _ _ _
      (seam_cons (r.beside (Row.straight X)) ih)
      (swap_row_sheet r q (p.padRight Y))

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
