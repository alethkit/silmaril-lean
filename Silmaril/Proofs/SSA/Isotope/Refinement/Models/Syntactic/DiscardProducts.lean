module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyStructure

/-! # Pure maps to unit and product-compatible discard -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- An affine input has a unique pure map to unit. The proof uses the
positive and negative instances of the written discard principle. -/
theorem pure_to_unit (hR : R.RenamingClosed) {A : τ}
    (f : Hom (ε := ε) F R A Silmaril.unit) (hf : hasEffect ⊥ f)
    (hA : Quantity.affine ≤ quantity A) : f = discard A hA := by
  have hu : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]
    exact le_top
  have hp := discard_natural hR .positive f hf hA hu (EffectSystem.canDelete_pure _)
  have hn := discard_natural hR .negative f hf hA hu (EffectSystem.canDelete_pure _)
  have he := le_antisymm hp hn
  rw [discard_unit hu, compose_identity] at he
  exact he

theorem discard_product (hR : R.RenamingClosed) (A B : τ)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (hAB : Quantity.affine ≤ quantity (product A B)) :
    discard (ε := ε) (F := F) (R := R) (product A B) hAB =
      compose hR
        (compose hR (right hR (discard A hA) B) (left hR Silmaril.unit (discard B hB)))
        (leftUnit Silmaril.unit) := by
  apply Eq.symm
  apply pure_to_unit hR _ _ hAB
  exact compose_effect hR
    (compose_effect hR (right_effect hR B (discard_pure A hA))
      (left_effect hR Silmaril.unit (discard_pure B hB))) (leftUnit_pure Silmaril.unit)

end Silmaril.Isotope.Refinement.Models.Syntactic
