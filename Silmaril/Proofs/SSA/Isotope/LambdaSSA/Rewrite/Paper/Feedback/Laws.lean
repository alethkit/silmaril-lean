module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Iteration equations at singleton state representatives -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem weakenTwice (p : Region Φ) :
    (p.renameVars (lift Nat.succ)).renameVars (lift (lift Nat.succ)) =
      (p.renameVars (lift Nat.succ)).renameVars (lift Nat.succ) := by
  rw [renameVars_comp, renameVars_comp]
  congr 1
  funext i
  cases i <;> rfl

theorem feedback_collapse {Γ : VCtx τ} {L : LCtx τ} {A : τ} {p : Region Φ}
    (hp : ValueBranches (A :: Γ) p (A :: A :: L)) :
    Eqv (A :: Γ) (feedbackRegion [A] (feedbackRegion [A] (fun _ => p)) 0)
      (feedbackRegion [A] (fun _ => p.renameLabels Nat.pred) 0) L := by
  have family : LSubst.ValueFamily Γ [A] (A :: A :: L) (fun _ => p) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hp
  have body := (family.liftVars A) (ℓ := 0) (A := A) rfl
  have entry : ValueBranches (A :: Γ) (.br 0 (.var 0) : Region Φ) (A :: L) :=
    .br rfl (.var rfl)
  have h := Eqv.collapsePost entry body (LSubst.HasType.id (Φ := Φ) (A :: Γ) L)
  simp only [lsubst_labelId, liftLSubstVars, CfgEta.Codiagonal.nested,
    CfgEta.Codiagonal.flattened, CfgEta.singleCfg] at h
  dsimp only [feedbackRegion, cfgEntryContinuations, List.length_cons, List.length_nil, renameVars]
  rw [weakenTwice, renameVars_renameLabels]
  simpa only [Fin.eq_zero, Fin.val_zero, Tm.rename, lift] using h

open CfgEta.Uniformity (enterSingle localMap)

private theorem renameLiftedFamily (σ : Nat → Region Φ) :
    (fun i => (liftLSubstVars σ i).renameVars (lift (lift Nat.succ))) =
      liftLSubstVars (fun i => (σ i).renameVars (lift Nat.succ)) := by
  funext i
  exact weakenTwice (σ i)

private theorem renameLocalMap (a : Tm Φ) :
    (fun i => (localMap a i).renameVars (lift Nat.succ)) =
      localMap (a.rename (lift Nat.succ)) := by
  funext i
  cases i <;> rfl

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem enterAfterBranch (a : Tm Φ) (q : Region Φ) {D : τ} :
    (Region.br 0 a).lsubst (liftLSubstVars (fun _ => feedbackRegion [D] (fun _ => q) 0)) =
      enterSingle a q := by
  simp only [lsubst, liftLSubstVars, feedbackRegion, cfgEntryContinuations, List.length_cons,
    List.length_nil, renameVars, substVars, Tm.rename, lift, enterSingle, CfgEta.singleCfg]
  have drop : Tm.liftSubst (Tm.singleSubst a) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [weakenTwice, substVars_renameVars, drop, substVars_var]
  rfl

theorem feedback_uniform {Γ : VCtx τ} {L : LCtx τ} {A D : τ}
    {p q : Region Φ} {a : Tm Φ}
    (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : HasType (D :: Γ) q (D :: L))
    (ha : Tm.BranchValue (A :: Γ) a D)
    (hs : Eqv (A :: Γ) (p.lsubst (liftLSubstVars (localMap a)))
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q))) (D :: L)) :
    Eqv (A :: Γ) (feedbackRegion [A] (fun _ => p) 0)
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => feedbackRegion [D] (fun _ => q) 0))) L := by
  let a' := a.rename (lift Nat.succ)
  let p' := p.renameVars (lift Nat.succ)
  let q' := q.renameVars (lift Nat.succ)
  have hp' : ValueBranches (A :: A :: Γ) p' (A :: L) := by
    have h : LSubst.ValueFamily Γ [A] (A :: L) (fun _ => p) :=
      fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hp
    exact (h.liftVars A) (ℓ := 0) (A := A) rfl
  have ha' : Tm.BranchValue (A :: A :: Γ) a' D := by
    have h : LSubst.ValueFamily Γ [A] [D] (fun _ => .br 0 a) := fun _ _ hi =>
      (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ (ValueBranches.br rfl ha)
    have hw : ValueBranches (A :: A :: Γ) (.br 0 a') [D] :=
      (h.liftVars A) (ℓ := 0) (A := A) rfl
    cases hw with
    | br hi hv => cases Option.some.inj hi; exact hv
  have hs' : Eqv (A :: A :: Γ) (p'.lsubst (liftLSubstVars (localMap a')))
      ((Region.br 0 a').lsubst (liftLSubstVars (fun _ => q'))) (D :: L) := by
    simpa only [p', q', a', renameVars_lsubst, renameLiftedFamily, renameLocalMap, renameVars] using
      hs.renameVars ((Ren.wk Γ A).lift A)
  have entry : ValueBranches (A :: Γ) (.br 0 (.var 0) : Region Φ) (A :: L) := .br rfl (.var rfl)
  have h := Eqv.uniform entry hp' (hq.renameVars ((Ren.wk Γ A).lift D)) ha' hs'
  have head : (Region.br 0 (.var 0)).lsubst (localMap a') = .br 0 a := by
    change Region.br 0 ((a.rename (lift Nat.succ)).subst (Tm.singleSubst (.var 0))) = .br 0 a
    rw [Tm.subst_rename]
    have drop : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
      funext i
      cases i <;> rfl
    rw [drop, Tm.subst_var]
  rw [head] at h
  rw [enterAfterBranch a q]
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper
