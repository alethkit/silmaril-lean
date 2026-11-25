module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.FreeTree
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

/-! # Reconstructing an expression after splitting a pure product slot -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit.Proofs

universe u v w
variable {τ : Type u} {Φ : Type v} {ε : Type w}

section Source

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {Γ : EffectCtx τ ε} {A B C : τ} {e : ε} {a b : Expr Φ}

omit [TypeFormers τ] in
public theorem splitCtx_pure (hΓ : Γ.Pure) (i : Fin Γ.length) (A B : τ) :
    (splitCtx Γ i A B).Pure := by
  intro j
  exact Fin.cases (motive := fun k => ((splitCtx Γ i A B).get k).2 = ⊥) rfl
    (SumSplit.branchCtx_pure hΓ i A) j

theorem split_typed (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) :
    TypedSubst (splitCtx Γ i A B) Γ (splitSubst i : Nat → Expr Φ) := by
  intro j
  by_cases hj : j.val = i.val
  · obtain rfl := Fin.ext hj
    have hp : Wf (splitCtx Γ j A B) (.var (j.val + 1) : Expr Φ) A (⊥ : ε) := by
      have hv := Wf.var (Φ := Φ) (Γ := SumSplit.branchCtx Γ j A)
        (j.cast List.length_set.symm) le_rfl
      have hw := wf_wk hv (Renaming.wk0 (SumSplit.branchCtx Γ j A) (B, ⊥))
      simpa only [Expr.wk, SumSplit.Proofs.branchCtx_lookup_self, Fin.val_cast] using hw
    have hq : Wf (splitCtx Γ j A B) (.var 0 : Expr Φ) B (⊥ : ε) := .var 0 le_rfl
    rw [ht, he]
    simpa [splitSubst] using Wf.pair hp hq
  · let j' : Fin (SumSplit.branchCtx Γ i A).length := j.cast List.length_set.symm
    have hget := SumSplit.Proofs.branchCtx_lookup_ne i j (Ne.symm hj) A
    have hv := Wf.var (Φ := Φ) (Γ := SumSplit.branchCtx Γ i A) j' le_rfl
    have hw := wf_wk hv (Renaming.wk0 (SumSplit.branchCtx Γ i A) (B, ⊥))
    simpa only [Expr.wk, splitSubst, ite_eq_right hj, j', hget, Fin.val_cast] using hw

theorem pair_beta_rebuild (i : Nat) (a : Expr Φ) :
    (((a.wk (SumSplit.toFront i)).wk1).wk1).subst
        (Expr.pair (.var 1) (.var 0)).subst0 =
      (split i a).wk (Expr.liftWk (SumSplit.toFront i)) := by
  simp only [Expr.wk1, wk_wk, subst_wk, split, wk_subst]
  congr 1
  funext j
  by_cases he : j = i
  · simp [Function.comp_apply, SumSplit.toFront, he, splitSubst, Expr.liftWk, Expr.subst0, Expr.wk]
  · simp [Function.comp_apply, SumSplit.toFront, he, splitSubst, Expr.liftWk, Expr.subst0, Expr.wk]

public theorem eqv_rebuild (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuild i a) := by
  let body := a.wk (SumSplit.toFront i)
  let v : Expr Φ := .var i.val
  let p : Expr Φ := .pair (.var 1) (.var 0)
  have hv : Wf Γ v (product A B) ⊥ := by
    simpa only [v, ht] using Wf.var (Φ := Φ) i he.le
  have hbody : Wf ((product A B, ⊥) :: Γ) body C e :=
    wf_wk ha (SumSplit.Proofs.ren_toFront i ht)
  have hpair : Wf ((B, ⊥) :: (A, ⊥) :: Γ) p (product A B) (⊥ : ε) :=
    .pair (.var 1 le_rfl) (.var 0 le_rfl)
  have hv' := wf_wkEff hv (show (⊥ : ε) ≤ e from bot_le)
  have hp' := wf_wkEff hpair (show (⊥ : ε) ≤ e from bot_le)
  have hEta : Eqv Γ (product A B) e (.let₂ v p) v :=
    .step (.rewrite (.let₂ hv' hp') hv' (.let2_eta v))
  have hRebind : Eqv Γ C e (.let₁ v body) a := by
    simpa only [v, body, SumSplit.Proofs.rebind_beta] using Eqv.step (Step.let1_beta hv hbody)
  have hw {Δ : EffectCtx τ ε} {X : τ} {b : Expr Φ}
      (hb : Wf ((product A B, ⊥) :: Δ) b C e) :
      Wf ((product A B, ⊥) :: (X, ⊥) :: Δ) b.wk1 C e :=
    wf_wk hb ((Renaming.wk0 Δ (X, ⊥)).lift (product A B, ⊥))
  have hww := hw (X := B) (hw (X := A) hbody)
  have hCommute : Eqv Γ C e (.let₁ (.let₂ v p) body) (.let₂ v (.let₁ p body.wk1.wk1)) :=
    .step (.rewrite (.let₁ (.let₂ hv' hp') hbody) (.let₂ hv' (.let₁ hp' hww))
      (.let1_let2 v p body))
  have hBeta : Eqv ((B, ⊥) :: (A, ⊥) :: Γ) C e (.let₁ p body.wk1.wk1)
      ((split i a).wk (Expr.liftWk (SumSplit.toFront i))) := by
    rw [← pair_beta_rebuild]
    exact .step (.let1_beta hpair hww)
  exact hRebind.symm.trans ((Eqv.let1 hEta.symm (.refl hbody)).trans
    (hCommute.trans (Eqv.let2 (.refl hv') hBeta)))

public theorem wf_split (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (splitCtx Γ i A B) (split i a) C e := wf_subst ha (split_typed i ht he)

public theorem eqv_iff_split (i : Fin Γ.length) (ht : (Γ.get i).1 = product A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔ Eqv (splitCtx Γ i A B) C e (split i a) (split i b) := by
  constructor
  · intro h
    exact eqv_subst h (split_typed i ht he)
  · intro h
    have hv : Wf Γ (.var i.val : Expr Φ) (product A B) e := by
      simpa only [ht] using Wf.var (Φ := Φ) i (he.trans_le bot_le)
    have h' := SumSplit.Proofs.eqv_rename h
      ((SumSplit.Proofs.ren_branch_toFront i A).lift (B, ⊥))
    exact (eqv_rebuild i ht he ha).trans
      ((Eqv.let2 (.refl hv) h').trans (eqv_rebuild i ht he hb).symm)

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
variable {Γ : EffectCtx τ ε} {A B C : τ} {a b : Expr Φ}

public theorem native_split (i : Fin Γ.length) (hΓ : Γ.Pure) (hty : (Γ.get i).1 = product A B)
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (h : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s C) :
    ∃ t' s' : Tm Empty Φ (splitCtx Γ i A B).length,
      (split i a).toLetIter (splitCtx Γ i A B).length = some t' ∧
      (split i b).toLetIter (splitCtx Γ i A B).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (splitCtx Γ i A B).toBoundCtx t' s' C :=
  SumSplit.TreeProofs.native_subst hΓ ht hs h (split_typed i hty (hΓ i))

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.ProductSplit.Proofs
