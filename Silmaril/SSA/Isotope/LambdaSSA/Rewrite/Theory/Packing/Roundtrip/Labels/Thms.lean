module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackingRoundtrip

/-! # The original labels of the packed continuation interface -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- At each exact label, the tagging continuation composed with the decoder
is the original forwarding continuation. -/
theorem unpack_packExits_pointwise (Γ : VCtx τ) (L : LCtx τ) :
    ∀ ⦃ℓ A⦄, At L ℓ A → SubstitutionEquiv (A :: Γ)
      (compLSubst (fun i => .br 0 (packedExitArg i (.var 0))) (fun _ => unpackExits L) ℓ)
      (labelId ℓ : Region Φ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpack_packExits_pointwise Γ L

end Silmaril.Isotope.LambdaSSA.Region
