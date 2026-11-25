module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Quotient
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Equivalence
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Moves

@[expose] public section

/-!
The algebraic comparison uses the existing seam moves, including for boxes
with empty boundaries. Its inverse schedules the generators and respects
the monoidal congruence by the two split witnesses for adjacent disjoint
rows. The comparison with embedded progressive plane graphs remains
separate, as do the extra runtime equations of Figure 9.
-/

namespace Silmaril.RuntimeWires.Sliced

open CategoryTheory

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B C X Y : List O}

/-- All algebraic arrows have a sheet representative, even with extra equations. -/
theorem Sheet.denote_surjective (E : Diagram.Equations S) :
    Function.Surjective (Sheet.denote (S := S) E (A := A) (B := B)) :=
  Proofs.SlicedCompleteness.representable E

/-- Sliced diagrams modulo seams present exactly the free monoidal term homs. -/
def SeamHom.termEquiv : SeamHom S A B ≃ Diagram.Hom S (noEquations S) A B where
  toFun := SeamHom.toTermHom
  invFun := SeamHom.fromTermHom
  left_inv := by exact Proofs.SlicedCompleteness.from_to
  right_inv := by exact Proofs.SlicedCompleteness.to_from

/-- Equality in the free monoidal presentation reflects seam equivalence. -/
theorem Sheet.denote_eq_iff {p q : Sheet S A B} :
    p.denote (noEquations S) = q.denote (noEquations S) ↔ Sheet.SeamEquivalent p q :=
  ⟨fun h => Quotient.exact (SeamHom.termEquiv.injective h),
    fun h => Sheet.SeamEquivalent.sound h _⟩

theorem Row.pass_straight (W Z : List O) :
    Row.pass W (Row.straight (S := S) Z) = Row.straight (W ++ Z) :=
  Proofs.SlicedCompleteness.pass_straight W Z

theorem Row.Split.pass (W : List O) {r : Row S A C} {p : Row S A B} {q : Row S B C}
    (h : Row.Split S r p q) : Row.Split S (Row.pass W r) (Row.pass W p) (Row.pass W q) :=
  Proofs.SlicedCompleteness.split_pass W h

theorem Row.Split.all_lower (r : Row S A B) : Row.Split S r (Row.straight A) r :=
  Proofs.SlicedCompleteness.split_all_lower r

theorem Sheet.SeamEquivalent.padLeft (W : List O) {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.padLeft W) (q.padLeft W) :=
  Proofs.SlicedCompleteness.seam_padLeft W h

theorem Sheet.SeamEquivalent.cons (r : Row S A B) {p q : Sheet S B C}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (.cons r p) (.cons r q) :=
  Proofs.SlicedCompleteness.seam_cons r h

theorem Sheet.SeamEquivalent.reindex (a : A = X) (b : B = Y) {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.reindex a b) (q.reindex a b) :=
  Proofs.SlicedCompleteness.seam_reindex a b h

theorem Sheet.SeamEquivalent.thenDo {p p' : Sheet S A B} {q q' : Sheet S B C}
    (h : Sheet.SeamEquivalent p p') (k : Sheet.SeamEquivalent q q') :
    Sheet.SeamEquivalent (p.thenDo q) (p'.thenDo q') :=
  Proofs.SlicedCompleteness.seam_then h k

theorem Sheet.reindex_single (a : A = X) (b : B = Y) (r : Row S A B) :
    (Sheet.cons r (.empty _)).reindex a b = .cons (r.reindex a b) (.empty _) := by
  subst a
  subst b
  rfl

/-- The two serializations of a horizontal pair of rows arise by splitting
the same joint row. -/
theorem Sheet.swap_rows {Z : List O} (r : Row S A B) (s : Row S X Y)
    (tail : Sheet S (B ++ Y) Z) :
    Sheet.SeamEquivalent
      (.cons (r.beside (Row.straight X)) (.cons (Row.pass B s) tail))
      (.cons (Row.pass A s) (.cons (r.beside (Row.straight Y)) tail)) :=
  Proofs.SlicedCompleteness.swap_rows r s tail

theorem SeamHom.toTermHom_comp (f : SeamHom S A B) (g : SeamHom S B C) :
    (f.comp g).toTermHom =
      ((show (⟨A⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨B⟩ from f.toTermHom) ≫
        (show (⟨B⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨C⟩ from g.toTermHom)) :=
  Proofs.SlicedCompleteness.toTerm_comp f g

theorem SeamHom.toTermHom_tensor (f : SeamHom S A B) (g : SeamHom S X Y) :
    (f.tensor g).toTermHom =
      Diagram.Presented.tensorMap
        (show (⟨A⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨B⟩ from f.toTermHom)
        (show (⟨X⟩ : Diagram.Presented S (noEquations S)) ⟶ ⟨Y⟩ from g.toTermHom) :=
  Proofs.SlicedCompleteness.toTerm_tensor f g

end Silmaril.RuntimeWires.Sliced

end

public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B X Y : List O}

/-- The ordered wire and generator labels of a row, independent of index transports. -/
def Row.cells (r : Row S A B) : List (O ⊕ S.Edge) :=
  Proofs.SlicedCompleteness.rowCells r

@[simp] theorem Row.cells_box (e : S.Edge) (r : Row S A B) :
    (Row.box e r).cells = Sum.inr e :: r.cells := by rfl

@[simp] theorem Row.cells_pass (W : List O) (r : Row S A B) :
    (Row.pass W r).cells = W.map Sum.inl ++ r.cells :=
  Proofs.SlicedCompleteness.pass_cells W r

@[simp] theorem Row.cells_straight (W : List O) :
    (Row.straight (S := S) W).cells = W.map Sum.inl :=
  Proofs.SlicedCompleteness.straight_cells W

@[simp] theorem Row.cells_beside (r : Row S A B) (q : Row S X Y) :
    (r.beside q).cells = r.cells ++ q.cells :=
  Proofs.SlicedCompleteness.beside_cells r q

/-- The ordered cells in each row determine a typed sheet. -/
def Sheet.cells (p : Sheet S A B) : List (List (O ⊕ S.Edge)) :=
  Proofs.SlicedCompleteness.sheetCells p

theorem Sheet.cells_injective : Function.Injective (Sheet.cells (S := S) (A := A) (B := B)) :=
  fun _ _ h => Proofs.SlicedCompleteness.sheet_ext h

@[simp] theorem Sheet.cells_empty : (Sheet.empty (S := S) A).cells = [] := by rfl

@[simp] theorem Sheet.cells_cons (r : Row S A B) (q : Sheet S B Y) :
    (Sheet.cons r q).cells = r.cells :: q.cells := by rfl

@[simp] theorem Sheet.cells_reindex (a : A = X) (b : B = Y) (q : Sheet S A B) :
    (q.reindex a b).cells = q.cells :=
  Proofs.SlicedCompleteness.sheet_reindex_cells a b q

theorem Sheet.cells_thenDo (p : Sheet S A B) (q : Sheet S B Y) :
    (p.thenDo q).cells = p.cells ++ q.cells :=
  Proofs.SlicedCompleteness.seq_cells p q

theorem Sheet.cells_padLeft (W : List O) (p : Sheet S A B) :
    (p.padLeft W).cells = p.cells.map (W.map Sum.inl ++ ·) :=
  Proofs.SlicedCompleteness.pad_left_cells W p

theorem Sheet.cells_padRight (p : Sheet S A B) (W : List O) :
    (p.padRight W).cells = p.cells.map (· ++ W.map Sum.inl) :=
  Proofs.SlicedCompleteness.pad_right_cells W p

/-- The left part is executed above the new seam and the right part below. -/
theorem Row.Split.left_first (r : Row S A B) (q : Row S X Y) :
    Row.Split S (r.beside q) (r.beside (Row.straight X)) (Row.pass B q) := by
  have h := Proofs.SlicedCompleteness.split_beside
    (Proofs.SlicedCompleteness.split_all_upper r) (Proofs.SlicedCompleteness.split_all_lower q)
  rwa [Proofs.SlicedCompleteness.straight_beside] at h

/-- The right part is executed above the new seam and the left part below. -/
theorem Row.Split.right_first (r : Row S A B) (q : Row S X Y) :
    Row.Split S (r.beside q) (Row.pass A q) (r.beside (Row.straight Y)) := by
  have h := Proofs.SlicedCompleteness.split_beside
    (Proofs.SlicedCompleteness.split_all_lower r) (Proofs.SlicedCompleteness.split_all_upper q)
  rwa [Proofs.SlicedCompleteness.straight_beside] at h

end Silmaril.RuntimeWires.Sliced
