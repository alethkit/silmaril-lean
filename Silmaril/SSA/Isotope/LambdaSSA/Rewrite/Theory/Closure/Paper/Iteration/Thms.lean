module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Feedback.Laws
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # Iteration equations on typed representatives in the paper relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open SyntacticCategory (iterateRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {A B : τ} {p : Region Φ}

/-- The literal fixpoint equation at every constructor-valued step. -/
theorem fixpoint (hp : ValueBranches (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p) (p.lsubst (fun _ => CfgEta.returnOrRepeat A p)) [B] :=
  .cfgEta (CfgEta.fixpoint hp)

/-- Arbitrary step regions enter the guarded iteration presentation after
binding their branch arguments. -/
theorem fixpoint_afterBinding (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p.bindBranchArguments)
      (p.bindBranchArguments.lsubst (fun _ => CfgEta.returnOrRepeat A p.bindBranchArguments)) [B] :=
  .cfgEta (CfgEta.fixpoint_afterBinding hp)

/-- Two feedback frames over the same singleton state can merge their
local labels while keeping an arbitrary outward exit interface. -/
theorem feedback_collapse {L : LCtx τ} (hp : ValueBranches (A :: Γ) p (A :: A :: L)) :
    Eqv (A :: Γ) (feedbackRegion [A] (feedbackRegion [A] (fun _ => p)) 0)
      (feedbackRegion [A] (fun _ => p.renameLabels Nat.pred) 0) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_collapse hp

/-- A constructor-valued state change that commutes with one step can
run before feedback. The simulation premise includes all outward exits. -/
theorem feedback_uniform {L : LCtx τ} {D : τ} {q : Region Φ} {a : Tm Φ}
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : HasType (D :: Γ) q (D :: L))
    (ha : Tm.BranchValue (A :: Γ) a D)
    (hs : Eqv (A :: Γ) (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)))
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q))) (D :: L)) :
    Eqv (A :: Γ) (feedbackRegion [A] (fun _ => p) 0)
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => feedbackRegion [D] (fun _ => q) 0))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_uniform hp hq ha hs

end Silmaril.Isotope.LambdaSSA.Region.Paper
