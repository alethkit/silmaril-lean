module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.IterationStrength

/-! # The native quantitative categorical iteration model -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} (hR : R.RenamingClosed) (cap : F.HasIter)

/-- Native uniformity supplies strength even for a linear retained object. -/
theorem typeIterCategory :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (ε := ε) (F := F) (R := R) hR
    letI := typeSymmetric (ε := ε) (F := F) (R := R) hR
    letI := typeHomOrder (ε := ε) (F := F) (R := R) hR
    IterCategory τ ε (typeEffects (ε := ε) (F := F) (R := R) hR)
      (chosenCoproducts hR (iter_hasCase cap)) (typeCaseCategory hR (iter_hasCase cap))
      (conwayIteration hR cap) := by
  let := category (ε := ε) F R hR
  let := typePremonoidal (ε := ε) (F := F) (R := R) hR
  let := typeSymmetric (ε := ε) (F := F) (R := R) hR
  let := typeHomOrder (ε := ε) (F := F) (R := R) hR
  refine { monotone := iterate_mono hR cap
           effect := fun he hf => iterate_effect hR cap he hf
           strength := ?_
           uniformity := ?_ }
  · intro D A B f
    let : IsIso ((chosenCoproducts (ε := ε) (F := F) (R := R) hR
        (iter_hasCase cap)).distributor D B A) :=
      (typeCaseCategory hR (iter_hasCase cap)).distributor_isIso D B A
    have hi : inv ((chosenCoproducts (ε := ε) (F := F) (R := R) hR
        (iter_hasCase cap)).distributor D B A) = distributorInv (iter_hasCase cap) D B A :=
      IsIso.inv_eq_of_hom_inv_id (distributor_distributorInv hR (iter_hasCase cap) D B A)
    change iterate (R := R) hR cap (compose (R := R) hR (left hR D f)
      (inv ((chosenCoproducts (ε := ε) (F := F) (R := R) hR
        (iter_hasCase cap)).distributor D B A))) = left hR D (iterate (R := R) hR cap f)
    rw [hi]
    exact iterate_strength hR cap D f
  · intro p e η A B D h f g he hm hh hf hs
    change p.orient (· ≤ ·) (compose (R := R) (@hR) h f)
      (compose (R := R) (@hR) g (desc (R := R) (@hR) (iter_hasCase cap)
        (compose (R := R) (@hR) (identity D) (inl (iter_hasCase cap) D B))
        (compose (R := R) (@hR) h (inr (iter_hasCase cap) D B)))) at hs
    have ht := congrArg (fun k : Hom (ε := ε) F R D (coprod D B) =>
      p.orient (· ≤ ·) (compose (R := R) (@hR) h f)
        (compose (R := R) (@hR) g (desc (R := R) (@hR) (iter_hasCase cap) k
          (compose (R := R) (@hR) h (inr (iter_hasCase cap) D B)))))
      (identity_compose (R := R) (@hR) (inl (iter_hasCase cap) D B))
    exact iterate_uniformity (@hR) cap p he hm hh hf (ht.mp hs)


/-- The literal typed quotient is a strong ordered effect-sensitive iterative model. -/
def iterModel : IterModel τ Φ ε where
  toCaseModel := caseModel (ε := ε) (F := F) (R := R) hR (iter_hasCase cap)
  iteration := conwayIteration hR cap
  iterLaws := typeIterCategory hR cap

@[simp] theorem iterModel_iterate {A B : τ} (f : Hom (ε := ε) F R A (coprod B A)) :
    (iterModel hR cap).iterate f = iterate (R := R) hR cap f := by
  change iterate (R := R) hR cap (compose (R := R) hR f (identity _)) = iterate (R := R) hR cap f
  rw [compose_identity]

end Silmaril.Isotope.Refinement.Models.Syntactic
