module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseStructure

/-! # Copy and discard respect the native coproduct type formers -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem discard_natural_pure (hR : R.RenamingClosed) {A B : τ}
    (f : Hom (ε := ε) F R A B) (hf : hasEffect ⊥ f)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B) :
    compose hR f (discard B hB) = discard A hA :=
  le_antisymm (discard_natural hR .positive f hf hA hB (EffectSystem.canDelete_pure .positive))
    (discard_natural hR .negative f hf hA hB (EffectSystem.canDelete_pure .negative))

theorem copy_natural_pure (hR : R.RenamingClosed) {A B : τ}
    (f : Hom (ε := ε) F R A B) (hf : hasEffect ⊥ f)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B) :
    compose hR f (copy B hB) =
      compose hR (copy A hA) (compose hR (right hR f A) (left hR B f)) :=
  le_antisymm (copy_natural hR .positive f hf hA hB (EffectSystem.canCopy_pure .positive))
    (copy_natural hR .negative f hf hA hB (EffectSystem.canCopy_pure .negative))

theorem discard_empty (cap : F.HasCase) (h : Quantity.affine ≤ quantity (Silmaril.empty : τ)) :
    discard (ε := ε) (F := F) (R := R) Silmaril.empty h = abort cap Silmaril.unit :=
  abort_unique cap _

theorem copy_empty (cap : F.HasCase) (h : Quantity.relevant ≤ quantity (Silmaril.empty : τ)) :
    copy (ε := ε) (F := F) (R := R) Silmaril.empty h =
      abort cap (product Silmaril.empty Silmaril.empty) :=
  abort_unique cap _

theorem discard_coprod (hR : R.RenamingClosed) (cap : F.HasCase) (A B : τ)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (hAB : Quantity.affine ≤ quantity (coprod A B)) :
    discard (ε := ε) (R := R) (coprod A B) hAB = desc hR cap (discard A hA) (discard B hB) :=
  desc_unique hR cap _ _ _
    (discard_natural_pure hR (inl cap A B) (inl_pure cap A B) hA hAB)
    (discard_natural_pure hR (inr cap A B) (inr_pure cap A B) hB hAB)

theorem copy_coprod (hR : R.RenamingClosed) (cap : F.HasCase) (A B : τ)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (hAB : Quantity.relevant ≤ quantity (coprod A B)) :
    copy (ε := ε) (R := R) (coprod A B) hAB = desc hR cap
      (compose hR (copy A hA) (compose hR (right hR (inl cap A B) A) (left hR (coprod A B) (inl cap A B))))
      (compose hR (copy B hB) (compose hR (right hR (inr cap A B) B) (left hR (coprod A B) (inr cap A B)))) :=
  desc_unique hR cap _ _ _
    (copy_natural_pure hR (inl cap A B) (inl_pure cap A B) hA hAB)
    (copy_natural_pure hR (inr cap A B) (inr_pure cap A B) hB hAB)

end Silmaril.Isotope.Refinement.Models.Syntactic
