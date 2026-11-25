module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs
public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! # Typed reconstruction of an expression by splitting on a sum slot -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.Proofs

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.Proofs

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

section Source

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

section CaseArms

variable {l r l' r' : Expr Φ}

public theorem caseArms_wf (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Wf Γ (caseArms i l r) C e := by
  have hvar : Wf Γ (.var i.val : Expr Φ) (coprod A B) e :=
    ht ▸ Wf.var i (he.trans_le bot_le)
  exact .case hvar (wf_wk hl (ren_branch_toFront i A)) (wf_wk hr (ren_branch_toFront i B))

private theorem arm_under_specialization (i : Nat) (p a : Expr Φ) :
    (a.wk (toFront i)).subst (Expr.liftSubst (replaceVar i p)) = a.wk (toFront i) := by
  have hc : Expr.liftSubst (replaceVar i p) ∘ toFront i =
      (Expr.var : Nat → Expr Φ) ∘ toFront i := by
    funext j
    by_cases h : j = i
    · simp [Function.comp_apply, toFront, h, Expr.liftSubst]
    · simp [Function.comp_apply, toFront, h, Expr.liftSubst, replaceVar, Expr.wk0, Expr.wk]
  rw [subst_wk, hc, ← subst_wk, subst_var]

private theorem specialized_arm_wf (i : Fin Γ.length) (p : Expr Φ)
    (hσ : TypedSubst (branchCtx Γ i X) Γ (replaceVar i p))
    (Y : τ) {arm : Expr Φ} (ha : Wf (branchCtx Γ i Y) arm C e) :
    Wf ((Y, ⊥) :: branchCtx Γ i X) (arm.wk (toFront i)) C e := by
  have h := wf_subst (wf_wk ha (ren_branch_toFront i Y)) (hσ.lift (Y, ⊥))
  rwa [arm_under_specialization i p arm] at h

private theorem payload_wf (i : Fin Γ.length) (X : τ) :
    Wf (branchCtx Γ i X) (.var i.val : Expr Φ) X (⊥ : ε) := by
  simpa only [branchCtx_lookup_self, Fin.val_cast] using
    (Wf.var (Φ := Φ) (Γ := branchCtx Γ i X) (i.cast List.length_set.symm) le_rfl)

public theorem caseArms_left (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Eqv (branchCtx Γ i A) C e (left i (caseArms i l r)) l := by
  let p : Expr Φ := .inl (.var i.val)
  have hσ : TypedSubst (branchCtx Γ i A) Γ (replaceVar i p) := left_typed i ht he
  have hl' := specialized_arm_wf i p hσ A hl
  have hr' := specialized_arm_wf i p hσ B hr
  have hvar := payload_wf (Φ := Φ) i A
  have hvar' := wf_wkEff hvar (show (⊥ : ε) ≤ e from bot_le)
  have hcase : Eqv (branchCtx Γ i A) C e
      (.case p (l.wk (toFront i)) (r.wk (toFront i))) (.let₁ (.var i.val) (l.wk (toFront i))) :=
    .step (.reduce (.case (.inl hvar') hl' hr') (.let₁ hvar' hl') (.case_inl _ _ _))
  have hbeta := Eqv.step (Step.let1_beta hvar hl')
  rw [rebind_beta] at hbeta
  have hexp : left i (caseArms i l r) = .case p (l.wk (toFront i)) (r.wk (toFront i)) := by
    simp only [left, caseArms, Expr.subst, arm_under_specialization, replaceVar, p]
    rfl
  exact hexp.symm ▸ hcase.trans hbeta

public theorem caseArms_right (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Eqv (branchCtx Γ i B) C e (right i (caseArms i l r)) r := by
  let p : Expr Φ := .inr (.var i.val)
  have hσ : TypedSubst (branchCtx Γ i B) Γ (replaceVar i p) := right_typed i ht he
  have hl' := specialized_arm_wf i p hσ A hl
  have hr' := specialized_arm_wf i p hσ B hr
  have hvar := payload_wf (Φ := Φ) i B
  have hvar' := wf_wkEff hvar (show (⊥ : ε) ≤ e from bot_le)
  have hcase : Eqv (branchCtx Γ i B) C e
      (.case p (l.wk (toFront i)) (r.wk (toFront i))) (.let₁ (.var i.val) (r.wk (toFront i))) :=
    .step (.reduce (.case (.inr hvar') hl' hr') (.let₁ hvar' hr') (.case_inr _ _ _))
  have hbeta := Eqv.step (Step.let1_beta hvar hr')
  rw [rebind_beta] at hbeta
  have hexp : right i (caseArms i l r) = .case p (l.wk (toFront i)) (r.wk (toFront i)) := by
    simp only [right, caseArms, Expr.subst, arm_under_specialization, replaceVar, p]
    rfl
  exact hexp.symm ▸ hcase.trans hbeta

public theorem caseArms_eqv_iff (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥)
    (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e)
    (hl' : Wf (branchCtx Γ i A) l' C e) (hr' : Wf (branchCtx Γ i B) r' C e) :
    Eqv Γ C e (caseArms i l r) (caseArms i l' r') ↔
      Eqv (branchCtx Γ i A) C e l l' ∧ Eqv (branchCtx Γ i B) C e r r' := by
  constructor
  · intro h
    have hs := (eqv_iff_specializations i ht he
      (caseArms_wf i ht he hl hr) (caseArms_wf i ht he hl' hr')).mp h
    exact ⟨(caseArms_left i ht he hl hr).symm.trans (hs.1.trans (caseArms_left i ht he hl' hr')),
      (caseArms_right i ht he hl hr).symm.trans (hs.2.trans (caseArms_right i ht he hl' hr'))⟩
  · rintro ⟨heL, heR⟩
    have hvar : Wf Γ (.var i.val : Expr Φ) (coprod A B) e :=
      ht ▸ Wf.var i (he.trans_le bot_le)
    exact .case (.refl hvar) (eqv_rename heL (ren_branch_toFront i A))
      (eqv_rename heR (ren_branch_toFront i B))

end CaseArms

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}

/-- A native equality transports through both pure sum-slot substitutions. -/
public theorem native_specializations {X Y Z : τ} (i : Fin Γ.length) (hΓ : Γ.Pure)
    (hi : (Γ.get i).1 = coprod X Y)
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) Γ.toBoundCtx t s Z) :
    (∃ t' s' : Tm Empty Φ (branchCtx Γ i X).length,
      (left i a).toLetIter (branchCtx Γ i X).length = some t' ∧
      (left i b).toLetIter (branchCtx Γ i X).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (branchCtx Γ i X).toBoundCtx t' s' Z) ∧
    (∃ t' s' : Tm Empty Φ (branchCtx Γ i Y).length,
      (right i a).toLetIter (branchCtx Γ i Y).length = some t' ∧
      (right i b).toLetIter (branchCtx Γ i Y).length = some s' ∧
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty τ) (branchCtx Γ i Y).toBoundCtx t' s' Z) :=
  ⟨Source.native_subst hΓ ht hs hn (left_typed i hi (hΓ i)),
    Source.native_subst hΓ ht hs hn (right_typed i hi (hΓ i))⟩

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit.Proofs
