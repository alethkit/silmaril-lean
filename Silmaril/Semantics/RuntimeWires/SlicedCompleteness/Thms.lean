module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Quotient
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Equivalence

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
