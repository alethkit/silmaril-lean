module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Typing

/-! # Syntax and typed contexts of the opt-in λSSA relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem Eqv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.typed h

/-- Replace the sole outgoing continuation of a fixed typed producer. -/
theorem lsubst_singleton_congr {Γ : VCtx τ} {L : LCtx τ} {A : τ} {p r s : Region Φ}
    (hp : ValueBranches Γ p [A]) (h : Eqv (A :: Γ) r s L) :
    Eqv Γ (p.lsubst (fun _ => r)) (p.lsubst (fun _ => s)) L :=
  .lsubstCongr hp fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ h

end Silmaril.Isotope.LambdaSSA.Region.Paper
