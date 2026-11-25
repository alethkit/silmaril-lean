module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SyntacticIteration

/-! # Region representatives of syntactic LambdaSSA iteration -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B : τ} {r : Region Φ}

/-- The one-label CFG loop preserves constructor-valued branch typing. -/
theorem iterateRegion_valueBranches (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    ValueBranches (A :: Γ) (iterateRegion A r) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.iterateRegion_valueBranches hr

/-- Iteration on native arrows has the explicit one-label CFG representative. -/
theorem iterate_ofRegion (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    iterate (ofRegion hr) = ofRegion (iterateRegion_valueBranches hr) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.iterate_ofRegion hr

/-- An arbitrary exactly typed step is evaluated through its bound representative. -/
theorem iterate_ofTypedRegion (hr : HasType (A :: Γ) r [Silmaril.coprod B A]) :
    iterate (ofTypedRegion hr) = ofRegion (iterateRegion_valueBranches hr.bindBranchArguments) :=
  iterate_ofRegion hr.bindBranchArguments

/-- Unfold the initial local branch while keeping the same feedback CFG. -/
theorem iterateRegion_unfold (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    SubstitutionEquiv (A :: Γ) (iterateRegion A r)
      (.cfg (iterationBody r) 1 (fun _ => (iterationBody r).renameVars (lift Nat.succ))) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.iterateRegion_unfold hr

/-- Move a one-label feedback CFG through the value decoder. A return leaves
the CFG immediately, and a repeat meets the same loop at the new state. -/
theorem iterationDispatch_cfg (hr : ValueBranches (A :: Γ) r [Silmaril.coprod B A]) :
    SubstitutionEquiv (Silmaril.coprod B A :: Γ)
      (.cfg iterationDispatch 1 (fun _ => (iterationBody r).renameVars (lift Nat.succ)))
      (.case (.var 0) (.br 0 (.var 0)) ((iterateRegion A r).renameVars (lift Nat.succ))) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.iterationDispatch_cfg hr

/-- An immediate left injection returns its payload without taking a repeat step. -/
theorem iterateRegion_return {b : Tm Φ} (hb : Tm.BranchValue (A :: Γ) b B) :
    SubstitutionEquiv (A :: Γ) (iterateRegion A (.br 0 (.inl b))) (.br 0 b) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.iterateRegion_return hb

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
