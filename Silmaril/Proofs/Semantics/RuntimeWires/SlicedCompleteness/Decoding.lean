module

public import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Algebra

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open CategoryTheory Silmaril.RuntimeWires.Sliced
open scoped MonoidalCategory

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Read each row as a term using its independent order of cells. -/
def rowTerm : {A B : List O} → Row S A B → Diagram S A B
  | _, _, .empty => .id []
  | _, _, .wire x r => .tensor (.id [x]) (rowTerm r)
  | _, _, .box e r => .tensor (.gen e) (rowTerm r)

/-- Read the rows from top to bottom as a term. -/
def sheetTerm : {A B : List O} → Sheet S A B → Diagram S A B
  | _, _, .empty A => .id A
  | _, _, .cons r p => .comp (rowTerm r) (sheetTerm p)

private def single {A B : List O} (r : Row S A B) : Sheet S A B := .cons r (.empty B)

private theorem single_tensor {A B X Y : List O} (r : Row S A B) (s : Row S X Y) :
    Sheet.SeamEquivalent ((single r).tensor (single s)) (single (r.beside s)) := by
  have h := split_beside (split_all_upper r) (split_all_lower s)
  rw [straight_beside] at h
  exact .symm _ _ (.rel _ _ (.split h (.empty _)))

private theorem tensor_reindex_left {A B X Y U V : List O} (a : A = X) (b : B = Y)
    (p : Sheet S A B) (q : Sheet S U V) :
    (p.tensor q).reindex (congrArg (· ++ U) a) (congrArg (· ++ V) b) =
      (p.reindex a b).tensor q := by
  subst a
  subst b
  rfl

private theorem single_box {A B : List O} (e : S.Edge) (r : Row S A B) :
    Sheet.SeamEquivalent ((Sheet.generator e).tensor (single r)) (single (.box e r)) := by
  let a := List.append_nil (S.source e)
  let b := List.append_nil (S.target e)
  have hs := seam_reindex (congrArg (· ++ A) a) (congrArg (· ++ B) b)
    (single_tensor (Row.box (S := S) e .empty) r)
  rw [tensor_reindex_left] at hs
  have ht : (single ((Row.box (S := S) e .empty).beside r)).reindex
      (congrArg (· ++ A) a) (congrArg (· ++ B) b) = single (.box e r) := by
    apply sheet_ext
    simp only [sheet_reindex_cells, single, sheetCells, beside_cells, rowCells, List.cons_append,
      List.nil_append]
  rw [ht] at hs
  exact hs

private theorem encode_row {A B : List O} (r : Row S A B) :
    Sheet.SeamEquivalent (Sheet.encode (rowTerm r)) (single r) := by
  induction r with
  | empty => exact .rel _ _ (.straight (.empty []))
  | wire x r ih =>
    have hs : Sheet.SeamEquivalent (Sheet.empty (S := S) [x]) (single (Row.straight [x])) :=
      .rel _ _ (.straight (.empty [x]))
    have hb := single_tensor (Row.straight [x]) r
    rw [straight_beside] at hb
    exact .trans _ _ _ (seam_tensor hs ih) hb
  | box e r ih =>
    exact .trans _ _ _ (seam_tensor (.refl (Sheet.generator e)) ih) (single_box e r)

theorem encode_sheet {A B : List O} (p : Sheet S A B) :
    Sheet.SeamEquivalent (Sheet.encode (sheetTerm p)) p := by
  induction p with
  | empty => exact .refl _
  | cons r p ih => exact seam_then (encode_row r) ih

variable (E : Diagram.Equations S)

local notation "Obj" => (Diagram.Presented.mk (S := S) (E := E))

private theorem rowTerm_denote {A B : List O} (r : Row S A B) :
    Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) (rowTerm r) = r.denote E := by
  induction r with
  | empty => rfl
  | @wire x A B r ih =>
    change (𝟙 (Obj [x])) ⊗ₘ (Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) (rowTerm r)) =
      (𝟙 (Obj [x])) ⊗ₘ (r.denote E)
    rw [ih]
  | @box e A B r ih =>
    let f : Obj (S.source e) ⟶ Obj (S.target e) := Diagram.Presented.ofTerm (.gen e)
    change f ⊗ₘ (Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) (rowTerm r)) = f ⊗ₘ (r.denote E)
    rw [ih]

theorem sheetTerm_denote {A B : List O} (p : Sheet S A B) :
    Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) (sheetTerm p) = p.denote E := by
  induction p with
  | empty => rfl
  | @cons A M B r p ih =>
    change Diagram.Presented.ofTerm (A := Obj A) (B := Obj M) (rowTerm r) ≫
      Diagram.Presented.ofTerm (A := Obj M) (B := Obj B) (sheetTerm p) = r.denote E ≫ p.denote E
    rw [rowTerm_denote, ih]

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
