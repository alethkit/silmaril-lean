module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Primitive.Defs
public import Mathlib.CategoryTheory.Monad.Basic

/-! # The fresh-generator monad on primitive dialects -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory

universe u

variable {τ ε : Type u} [HasUnit τ]
variable {P Q : InstrSig τ ε} {e : ε}

/-- A dialect map out of the extension is uniquely determined by its restriction
and the profiled image of each new instruction. -/
theorem extendDialect_unique (f : P ⟶ Q) (c : (A : τ) → UBInstruction Q e A)
    (g : dialect P e ⟶ Q) (h : includeDialect P e ≫ g = f)
    (hc : ∀ A, InstrSig.Hom.instr g (.inr A) = (c A).val) : g = extendDialect f c := by
  subst f
  exact InstrSig.Hom.ext (funext (Sum.rec (fun _ => rfl) hc))

/-- The monad on primitive dialects at fixed types, effects, and UB effect.
It adds instruction symbols. The ordered specification monad adds the inequations. -/
def dialectMonad (e : ε) : Monad (InstrSig τ ε) where
  obj P := dialect P e
  map f := extendDialect (f ≫ includeDialect _ e) (fun A => ⟨.inr A, rfl, rfl, rfl⟩)
  map_id _ := InstrSig.Hom.ext (funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))
  map_comp _ _ := InstrSig.Hom.ext (funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))
  η := { app P := includeDialect P e, naturality _ _ _ := rfl }
  μ := {
    app P := extendDialect (𝟙 (dialect P e)) (fun A => ⟨.inr A, rfl, rfl, rfl⟩)
    naturality _ _ _ := InstrSig.Hom.ext (funext (Sum.rec
      (Sum.rec (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl))) }
  assoc _ := InstrSig.Hom.ext (funext (Sum.rec
    (Sum.rec (Sum.rec (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl)) (fun _ => rfl)))
  left_unit _ := rfl
  right_unit _ := InstrSig.Hom.ext (funext (Sum.rec (fun _ => rfl) (fun _ => rfl)))

end Silmaril.Isotope.Institution.Refinement.UB
