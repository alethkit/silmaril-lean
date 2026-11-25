module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

def rowCells : {A B : List O} → Row S A B → List (O ⊕ S.Edge)
  | _, _, .empty => []
  | _, _, .wire x r => .inl x :: rowCells r
  | _, _, .box e r => .inr e :: rowCells r

def inputCells (S : Signature.{u,v} O) : List (O ⊕ S.Edge) → List O
  | [] => []
  | .inl x :: cells => x :: inputCells S cells
  | .inr e :: cells => S.source e ++ inputCells S cells

def outputCells (S : Signature.{u,v} O) : List (O ⊕ S.Edge) → List O
  | [] => []
  | .inl x :: cells => x :: outputCells S cells
  | .inr e :: cells => S.target e ++ outputCells S cells

theorem rowInputs {A B : List O} (r : Row S A B) : inputCells S (rowCells r) = A := by
  induction r with
  | empty => rfl
  | wire x r ih => exact congrArg (x :: ·) ih
  | box e r ih => exact congrArg (S.source e ++ ·) ih

theorem rowOutputs {A B : List O} (r : Row S A B) : outputCells S (rowCells r) = B := by
  induction r with
  | empty => rfl
  | wire x r ih => exact congrArg (x :: ·) ih
  | box e r ih => exact congrArg (S.target e ++ ·) ih

private theorem row_heq {A B X Y : List O} (r : Row S A B) (q : Row S X Y)
    (h : rowCells r = rowCells q) : HEq r q := by
  induction r generalizing X Y with
  | empty =>
    cases q <;> simp only [rowCells, reduceCtorEq] at h
    rfl
  | @wire x A B r ih =>
    cases q with
    | empty => simp only [rowCells, List.cons_ne_nil] at h
    | box e q => simp only [rowCells, List.cons.injEq, reduceCtorEq, false_and] at h
    | @wire y X Y q =>
      have cells := (List.cons.inj h).2
      have label := Sum.inl.inj (List.cons.inj h).1
      have input := (rowInputs r).symm.trans ((congrArg (inputCells S) cells).trans (rowInputs q))
      have output := (rowOutputs r).symm.trans ((congrArg (outputCells S) cells).trans (rowOutputs q))
      subst label
      subst input
      subst output
      cases eq_of_heq (ih q cells)
      rfl
  | @box e A B r ih =>
    cases q with
    | empty => simp only [rowCells, List.cons_ne_nil] at h
    | wire x q => simp only [rowCells, List.cons.injEq, reduceCtorEq, false_and] at h
    | @box f X Y q =>
      have cells := (List.cons.inj h).2
      have label := Sum.inr.inj (List.cons.inj h).1
      have input := (rowInputs r).symm.trans ((congrArg (inputCells S) cells).trans (rowInputs q))
      have output := (rowOutputs r).symm.trans ((congrArg (outputCells S) cells).trans (rowOutputs q))
      subst label
      subst input
      subst output
      cases eq_of_heq (ih q cells)
      rfl

theorem row_ext {A B : List O} {r q : Row S A B} (h : rowCells r = rowCells q) : r = q :=
  eq_of_heq (row_heq r q h)

def sheetCells : {A B : List O} → Sheet S A B → List (List (O ⊕ S.Edge))
  | _, _, .empty _ => []
  | _, _, .cons r p => rowCells r :: sheetCells p

theorem sheet_ext {A B : List O} {p q : Sheet S A B}
    (h : sheetCells p = sheetCells q) : p = q := by
  induction p with
  | empty =>
    cases q with
    | empty => rfl
    | cons r q => simp only [sheetCells, reduceCtorEq] at h
  | @cons A M B r p ih =>
    cases q with
    | empty => simp only [sheetCells, List.cons_ne_nil] at h
    | @cons _ N _ s q =>
      obtain ⟨head, tail⟩ := List.cons.inj h
      have middle := (rowOutputs r).symm.trans ((congrArg (outputCells S) head).trans (rowOutputs s))
      subst middle
      cases row_ext head
      cases ih tail
      rfl

@[simp] theorem row_reindex_cells {A B X Y : List O} (p : A = X) (q : B = Y) (r : Row S A B) :
    rowCells (r.reindex p q) = rowCells r := by
  subst p
  subst q
  rfl

@[simp] theorem sheet_reindex_cells {A B X Y : List O} (p : A = X) (q : B = Y) (r : Sheet S A B) :
    sheetCells (r.reindex p q) = sheetCells r := by
  subst p
  subst q
  rfl

@[simp] theorem straight_cells (W : List O) :
    rowCells (Row.straight (S := S) W) = W.map Sum.inl := by
  induction W with
  | nil => rfl
  | cons x W ih => exact congrArg (Sum.inl x :: ·) ih

@[simp] theorem pass_cells (W : List O) {A B : List O} (r : Row S A B) :
    rowCells (Row.pass W r) = W.map Sum.inl ++ rowCells r := by
  induction W with
  | nil => rfl
  | cons x W ih => exact congrArg (Sum.inl x :: ·) ih

@[simp] theorem beside_cells {A B X Y : List O} (r : Row S A B) (q : Row S X Y) :
    rowCells (r.beside q) = rowCells r ++ rowCells q := by
  induction r with
  | empty => rfl
  | wire x r ih => exact congrArg (Sum.inl x :: ·) ih
  | box e r ih => simp only [Row.beside, row_reindex_cells, rowCells, List.cons_append, ih]

@[simp] theorem seq_cells {A B C : List O} (p : Sheet S A B) (q : Sheet S B C) :
    sheetCells (p.thenDo q) = sheetCells p ++ sheetCells q := by
  induction p with
  | empty => rfl
  | cons r p ih => exact congrArg (rowCells r :: ·) (ih q)

@[simp] theorem pad_left_cells (W : List O) {A B : List O} (p : Sheet S A B) :
    sheetCells (p.padLeft W) = (sheetCells p).map (W.map Sum.inl ++ ·) := by
  induction p with
  | empty => rfl
  | cons r p ih =>
    simp only [Sheet.padLeft, sheetCells, List.map_cons, pass_cells, ih]

@[simp] theorem pad_right_cells (W : List O) {A B : List O} (p : Sheet S A B) :
    sheetCells (p.padRight W) = (sheetCells p).map (· ++ W.map Sum.inl) := by
  induction p with
  | empty => rfl
  | cons r p ih =>
    simp only [Sheet.padRight, sheetCells, List.map_cons, beside_cells, straight_cells, ih]

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
