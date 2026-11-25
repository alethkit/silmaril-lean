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

theorem Sheet.SeamEquivalent.cons (r : Row S A B) {p q : Sheet S B C}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (.cons r p) (.cons r q) :=
  Proofs.SlicedCompleteness.seam_cons r h

theorem Sheet.SeamEquivalent.reindex (a : A = X) (b : B = Y) {p q : Sheet S A B}
    (h : Sheet.SeamEquivalent p q) : Sheet.SeamEquivalent (p.reindex a b) (q.reindex a b) :=
  Proofs.SlicedCompleteness.seam_reindex a b h

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
