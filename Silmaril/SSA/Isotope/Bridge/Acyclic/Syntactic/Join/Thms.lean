module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.GuardedJoin

/-! # The exact guarded equation for a nonrecursive one-block join -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {A : τ}

/-- Enter the outward-only block with the result of the singleton entry.
The block's free label shift puts every exit outside the newly bound label. -/
theorem linkedJoin {entry block : Region Φ}
    (he : ValueBranches Γ entry [A]) (hb : ValueBranches (A :: Γ) block L) :
    Eqv Γ (CfgEta.singleCfg entry (block.renameLabels Nat.succ))
      (entry.lsubst (fun _ => block)) L :=
  Proofs.SSA.Isotope.Bridge.Acyclic.GuardedJoin.link he hb

end Silmaril.Isotope.LambdaSSA.Region.Paper
