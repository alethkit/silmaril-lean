module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport

/-! # Typed renaming and guarded composition in the paper relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Compose pointwise equivalent continuation families. Changing the first
family requires constructor-valued branches on both of its representatives. -/
theorem compLSubst_congr {Γ : VCtx τ} {L K P : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (σ i) (σ' i) K)
    (hυ : ∀ ⦃i A⦄, At K i A → Eqv (A :: Γ) (υ i) (υ' i) P)
    (hsource : LSubst.ValueFamily Γ L K σ) (htarget : LSubst.ValueFamily Γ L K σ') :
    ∀ ⦃i A⦄, At L i A → Eqv (A :: Γ) (compLSubst σ υ i) (compLSubst σ' υ' i) P :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Transport.compLSubst_congr hσ hυ hsource htarget

end Silmaril.Isotope.LambdaSSA.Region.Paper
