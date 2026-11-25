module

public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Cells

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

theorem pass_straight (W Z : List O) :
    Row.pass W (Row.straight (S := S) Z) = Row.straight (W ++ Z) :=
  row_ext (by simp only [pass_cells, straight_cells, List.map_append])

theorem straight_beside (W : List O) {A B : List O} (r : Row S A B) :
    (Row.straight W).beside r = Row.pass W r :=
  row_ext (by simp only [beside_cells, pass_cells, straight_cells])

theorem split_all_upper {A B : List O} (r : Row S A B) : Row.Split S r r (Row.straight B) := by
  induction r with
  | empty => exact .empty
  | wire x r ih => exact .wire x ih
  | box e r ih => simpa only [pass_straight] using Row.Split.upper e ih

theorem split_all_lower {A B : List O} (r : Row S A B) : Row.Split S r (Row.straight A) r := by
  induction r with
  | empty => exact .empty
  | wire x r ih => exact .wire x ih
  | box e r ih => simpa only [pass_straight] using Row.Split.lower e ih

theorem split_straight (W : List O) :
    Row.Split S (Row.straight W) (Row.straight W) (Row.straight W) := by
  induction W with
  | nil => exact .empty
  | cons x W ih => exact .wire x ih

theorem split_pass (W : List O) {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (h : Row.Split S r p q) : Row.Split S (Row.pass W r) (Row.pass W p) (Row.pass W q) := by
  induction W with
  | nil => exact h
  | cons x W ih => exact .wire x ih

private theorem split_align {A M B A' M' B' : List O}
    {r : Row S A B} {p : Row S A M} {q : Row S M B}
    {r' : Row S A' B'} {p' : Row S A' M'} {q' : Row S M' B'}
    (h : Row.Split S r p q) (a : A = A') (m : M = M') (b : B = B')
    (hr : rowCells r = rowCells r') (hp : rowCells p = rowCells p') (hq : rowCells q = rowCells q') :
    Row.Split S r' p' q' := by
  subst a
  subst m
  subst b
  cases row_ext hr
  cases row_ext hp
  cases row_ext hq
  exact h

theorem split_beside {A M B X T Y : List O}
    {r : Row S A B} {p : Row S A M} {q : Row S M B}
    {s : Row S X Y} {f : Row S X T} {g : Row S T Y}
    (h : Row.Split S r p q) (k : Row.Split S s f g) :
    Row.Split S (r.beside s) (p.beside f) (q.beside g) := by
  induction h with
  | empty => exact k
  | wire x h ih => exact .wire x ih
  | upper e h ih =>
    refine split_align (Row.Split.upper e ih) (List.append_assoc ..).symm
      (List.append_assoc ..).symm (List.append_assoc ..).symm ?_ ?_ ?_
    · simp only [rowCells, beside_cells, List.cons_append]
    · simp only [rowCells, beside_cells, List.cons_append]
    · simp only [pass_cells, beside_cells, List.append_assoc]
  | lower e h ih =>
    refine split_align (Row.Split.lower e ih) (List.append_assoc ..).symm
      (List.append_assoc ..).symm (List.append_assoc ..).symm ?_ ?_ ?_
    · simp only [rowCells, beside_cells, List.cons_append]
    · simp only [pass_cells, beside_cells, List.append_assoc]
    · simp only [rowCells, beside_cells, List.cons_append]

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
