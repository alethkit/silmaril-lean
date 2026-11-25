module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations

/-! # Typed reconstruction of an expression by splitting on a sum slot -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.Proofs

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε} {a b : Expr Φ}

omit [TypeFormers τ] in
public theorem branchCtx_lookup_self (i : Fin Γ.length) (X : τ) :
    (branchCtx Γ i X).get (i.cast (List.length_set.symm)) = (X, ⊥) := by
  exact List.getElem_set_self _

omit [TypeFormers τ] in
public theorem branchCtx_lookup_ne (i j : Fin Γ.length) (hij : i.val ≠ j.val) (X : τ) :
    (branchCtx Γ i X).get (j.cast (List.length_set.symm)) = Γ.get j := by
  exact List.getElem_set_ne hij _

omit [TypeFormers τ] in
public theorem branchCtx_pure (hΓ : Γ.Pure) (i : Fin Γ.length) (X : τ) :
    (branchCtx Γ i X).Pure := by
  intro j
  let j' : Fin Γ.length := j.cast List.length_set
  have hj : j = j'.cast List.length_set.symm := Fin.ext rfl
  rw [hj]
  by_cases he : i.val = j'.val
  · rw [← Fin.ext he, branchCtx_lookup_self]
  · rw [branchCtx_lookup_ne i j' he]
    exact hΓ j'

omit [TypeFormers τ] in
public theorem ren_toFront (i : Fin Γ.length) (ht : (Γ.get i).1 = X) :
    Renaming ((X, ⊥) :: Γ) Γ (toFront i) := by
  intro j
  by_cases hj : j.val = i.val
  · obtain rfl := Fin.ext hj
    exact ⟨0, ite_eq_left rfl, ht.symm, bot_le⟩
  · exact ⟨j.succ, ite_eq_right hj, rfl, le_rfl⟩

omit [TypeFormers τ] in
public theorem ren_branch_toFront (i : Fin Γ.length) (X : τ) :
    Renaming ((X, ⊥) :: Γ) (branchCtx Γ i X) (toFront i) := by
  intro j
  let j' : Fin Γ.length := j.cast List.length_set
  have hj' : j = j'.cast List.length_set.symm := Fin.ext rfl
  by_cases hj : j'.val = i.val
  · have hji : j = i.cast List.length_set.symm := Fin.ext hj
    rw [hji, branchCtx_lookup_self]
    exact ⟨0, ite_eq_left rfl, rfl, le_rfl⟩
  · rw [hj', branchCtx_lookup_ne i j' (Ne.symm hj)]
    exact ⟨j'.succ, ite_eq_right hj, rfl, le_rfl⟩

public theorem eqv_rename {Δ : EffectCtx τ ε} {ξ : Nat → Nat}
    (h : Eqv Δ C e a b) (hr : Renaming Γ Δ ξ) :
    Eqv Γ C e (a.wk ξ) (b.wk ξ) := by
  have hs : TypedSubst Γ Δ (Expr.var ∘ ξ : Nat → Expr Φ) := by
    intro i
    obtain ⟨j, hj, hty, he⟩ := hr i
    simpa only [Function.comp_apply, hj, hty] using Wf.var j he
  simpa only [← subst_wk, subst_var] using eqv_subst h hs

theorem replaceVar_typed (i : Fin Γ.length) {p : Expr Φ}
    (hp : Wf (branchCtx Γ i X) p (Γ.get i).1 (Γ.get i).2) :
    TypedSubst (branchCtx Γ i X) Γ (replaceVar i p) := by
  intro j
  by_cases hj : j.val = i.val
  · obtain rfl := Fin.ext hj
    simpa [replaceVar] using hp
  · let j' : Fin (branchCtx Γ i X).length := j.cast List.length_set.symm
    have hget := branchCtx_lookup_ne i j (Ne.symm hj) X
    have hv : Wf (branchCtx Γ i X) (.var j.val : Expr Φ) (Γ.get j).1 (Γ.get j).2 := by
      simpa only [j', hget, Fin.val_cast] using Wf.var (Γ := branchCtx Γ i X) j' le_rfl
    simpa only [replaceVar, ite_eq_right hj] using hv

public theorem left_typed (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) :
    TypedSubst (branchCtx Γ i A) Γ (replaceVar i (.inl (.var i) : Expr Φ)) := by
  apply replaceVar_typed
  rw [ht, he]
  apply Wf.inl
  simpa only [branchCtx_lookup_self, Fin.val_cast] using
    Wf.var (Φ := Φ) (Γ := branchCtx Γ i A) (i.cast List.length_set.symm) le_rfl

public theorem right_typed (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) :
    TypedSubst (branchCtx Γ i B) Γ (replaceVar i (.inr (.var i) : Expr Φ)) := by
  apply replaceVar_typed
  rw [ht, he]
  apply Wf.inr
  simpa only [branchCtx_lookup_self, Fin.val_cast] using
    Wf.var (Φ := Φ) (Γ := branchCtx Γ i B) (i.cast List.length_set.symm) le_rfl

public theorem rebind_beta (i : Nat) (a : Expr Φ) :
    (a.wk (toFront i)).subst (.var i : Expr Φ).subst0 = a := by
  rw [subst_wk]
  have h : ((.var i : Expr Φ).subst0 ∘ toFront i) = Expr.var := by
    funext j
    by_cases he : j = i
    · simp [toFront, he, Expr.subst0]
    · simp [toFront, he, Expr.subst0]
  rw [h, subst_var]

theorem branch_beta (i : Nat) (a : Expr Φ) (inj : Expr Φ → Expr Φ)
    (hinj : ∀ j ξ, (inj (.var j)).wk ξ = inj (.var (ξ j))) :
    ((a.wk (toFront i)).wk1).subst (inj (.var 0)).subst0 =
      ((a.subst (replaceVar i (inj (.var i)))).wk (toFront i)) := by
  rw [Expr.wk1, wk_wk, subst_wk, wk_subst]
  congr 1
  funext j
  by_cases he : j = i
  · simp [Function.comp_apply, toFront, he, replaceVar, Expr.liftWk, Expr.subst0, hinj]
  · simp [Function.comp_apply, toFront, he, replaceVar, Expr.liftWk, Expr.subst0, Expr.wk]

public theorem eqv_rebuild (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuild i a) := by
  let body := a.wk (toFront i)
  let v : Expr Φ := .var i.val
  let lv : Expr Φ := .inl (.var 0)
  let rv : Expr Φ := .inr (.var 0)
  have hv : Wf Γ v (coprod A B) ⊥ := by
    simpa only [v, ht] using Wf.var (Φ := Φ) i he.le
  have hbody : Wf ((coprod A B, ⊥) :: Γ) body C e := wf_wk ha (ren_toFront i ht)
  have hL {Δ : EffectCtx τ ε} : Wf ((A, ⊥) :: Δ) lv (coprod A B) ⊥ :=
    .inl (.var 0 le_rfl)
  have hR {Δ : EffectCtx τ ε} : Wf ((B, ⊥) :: Δ) rv (coprod A B) ⊥ :=
    .inr (.var 0 le_rfl)
  have hv' := wf_wkEff hv (show (⊥ : ε) ≤ e from bot_le)
  have hcase : Wf Γ (.case v lv rv) (coprod A B) e :=
    .case hv' (wf_wkEff hL bot_le) (wf_wkEff hR bot_le)
  have hEta : Eqv Γ (coprod A B) e (.case v lv rv) v :=
    .step (.rewrite hcase hv' (.case_eta v))
  have hRebind : Eqv Γ C e (.let₁ v body) a := by
    simpa only [v, body, rebind_beta] using Eqv.step (Step.let1_beta hv hbody)
  have hw {X : τ} : Wf ((coprod A B, ⊥) :: (X, ⊥) :: Γ) body.wk1 C e :=
    wf_wk hbody ((Renaming.wk0 Γ (X, ⊥)).lift (coprod A B, ⊥))
  have hCommute : Eqv Γ C e (.let₁ (.case v lv rv) body)
      (.case v (.let₁ lv body.wk1) (.let₁ rv body.wk1)) :=
    .step (.rewrite (.let₁ hcase hbody)
      (.case hv' (.let₁ (wf_wkEff hL bot_le) hw) (.let₁ (wf_wkEff hR bot_le) hw))
      (.let1_case v lv rv body))
  have hBetaL : Eqv ((A, ⊥) :: Γ) C e (.let₁ lv body.wk1) ((left i a).wk (toFront i)) := by
    rw [left, ← branch_beta i a .inl (fun _ _ => rfl)]
    exact .step (.let1_beta hL hw)
  have hBetaR : Eqv ((B, ⊥) :: Γ) C e (.let₁ rv body.wk1) ((right i a).wk (toFront i)) := by
    rw [right, ← branch_beta i a .inr (fun _ _ => rfl)]
    exact .step (.let1_beta hR hw)
  exact hRebind.symm.trans ((Eqv.let1 hEta.symm (.refl hbody)).trans
    (hCommute.trans (Eqv.case (.refl hv') hBetaL hBetaR)))

public theorem eqv_iff_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔
      Eqv (branchCtx Γ i A) C e (left i a) (left i b) ∧
      Eqv (branchCtx Γ i B) C e (right i a) (right i b) := by
  constructor
  · intro h
    exact ⟨eqv_subst h (left_typed i ht he), eqv_subst h (right_typed i ht he)⟩
  · rintro ⟨hl, hr⟩
    have hv : Wf Γ (.var i.val : Expr Φ) (coprod A B) e := by
      simpa only [ht] using Wf.var (Φ := Φ) i (he.trans_le bot_le)
    exact (eqv_rebuild i ht he ha).trans ((Eqv.case (.refl hv)
      (eqv_rename hl (ren_branch_toFront i A)) (eqv_rename hr (ren_branch_toFront i B))).trans
      (eqv_rebuild i ht he hb).symm)


/-- The two specializations are typed at the same effect bound. -/
public theorem wf_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (branchCtx Γ i A) (left i a) C e ∧ Wf (branchCtx Γ i B) (right i a) C e :=
  ⟨wf_subst ha (left_typed i ht he), wf_subst ha (right_typed i ht he)⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.Proofs
