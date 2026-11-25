module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Closure

/-! # Substitution and fixpoint in the one-block CFG η presentation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open Silmaril.DeBruijn (lift)
open SyntacticCategory (iterateRegion)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- One-block CFG η is the identity-substitution instance of the new scheme. -/
theorem Eqv.eta {Γ : VCtx τ} {L : LCtx τ} {A : τ} {entry block : Region Φ}
    (he : ValueBranches Γ entry (A :: L)) (hb : ValueBranches (A :: Γ) block (A :: L)) :
    Eqv Γ (singleCfg entry block) (entry.lsubst (reentry block)) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eta he hb

/-- Both sides of an equation have the same exact input and exit interfaces. -/
theorem Eqv.typed {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} (h : Eqv Γ r s L) :
    HasType Γ r L ∧ HasType Γ s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_typed h

/-- Apply any exactly typed outgoing continuation family to both sides. -/
theorem Eqv.lsubst {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {σ : Nat → Region Φ} (hσ : LSubst.HasType Γ L K σ) :
    Eqv Γ (r.lsubst σ) (s.lsubst σ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_lsubst h hσ

/-- Apply simultaneous value substitution with constructor-valued images. -/
theorem Eqv.substVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {θ : Nat → Tm Φ}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) :
    Eqv Δ (r.substVars θ) (s.substVars θ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_substVars h hθ

/-- Typed value renaming preserves the extended relation. -/
theorem Eqv.renameVars {Γ Δ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ) :
    Eqv Δ (r.renameVars ρ) (s.renameVars ρ) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_renameVars h hρ

/-- Typed free-label renaming preserves the extended relation. -/
theorem Eqv.renameLabels {Γ : VCtx τ} {L K : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    Eqv Γ (r.renameLabels ρ) (s.renameLabels ρ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_renameLabels h hρ

/-- Replace pointwise equivalent continuations at constructor-valued branches. -/
theorem lsubst_congr {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) {σ υ : Nat → Region Φ} (h : Equivalent Γ L K σ υ) :
    Eqv Γ (r.lsubst σ) (r.lsubst υ) K :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.lsubst_congr hr h

/-- Binding branch arguments preserves the extended relation. -/
theorem Eqv.bindBranchArguments {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Eqv Γ r s L) : Eqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.eqv_bindBranchArguments h

/-- Composition of value-branch continuation families respects pointwise equivalence. -/
theorem Equivalent.comp {Γ : VCtx τ} {L K H : LCtx τ} {σ σ' υ υ' : Nat → Region Φ}
    (hσ : Equivalent Γ L K σ σ') (hυ : Equivalent Γ K H υ υ')
    (hvalues : LSubst.ValueFamily Γ L K σ) :
    Equivalent Γ L H (compLSubst σ υ) (compLSubst σ' υ') :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.equivalent_comp hσ hυ hvalues

/-- Move a one-block CFG through sequencing with a singleton-exit producer.
The producer, decoder and block may themselves contain recursive CFGs. -/
theorem seqCont {Γ : VCtx τ} {A S : τ} {L : LCtx τ} {p d b : Region Φ}
    (hp : ValueBranches Γ p [S]) (hd : ValueBranches (S :: Γ) d (A :: L))
    (hb : ValueBranches (A :: Γ) b (A :: L)) :
    Eqv Γ (singleCfg (p.lsubst (fun _ => d)) b)
      (p.lsubst (fun _ => singleCfg d (b.renameVars (lift Nat.succ)))) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.seqCont hp hd hb

/-- Literal fixpoint for every step from `A :: Γ` to the singleton sum exit
`[coprod B A]` whose branch arguments are constructor values. Effects in
computations and nested CFGs are allowed. -/
theorem fixpoint {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : ValueBranches (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p) (p.lsubst (fun _ => returnOrRepeat A p)) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.fixpoint hp

/-- Every exactly typed step with singleton sum exit satisfies the literal
fixpoint equation after binding its branch arguments. -/
theorem fixpoint_afterBinding {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : HasType (A :: Γ) p [Silmaril.coprod B A]) :
    Eqv (A :: Γ) (iterateRegion A p.bindBranchArguments)
      (p.bindBranchArguments.lsubst (fun _ => returnOrRepeat A p.bindBranchArguments)) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.fixpoint_afterBinding hp

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
