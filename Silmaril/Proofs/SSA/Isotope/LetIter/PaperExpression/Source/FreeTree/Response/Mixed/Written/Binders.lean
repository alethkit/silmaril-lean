module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Bind

/-! # Typed conversions used by the written mixed normalizer -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall (SumSignature endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {A B C : Ty α} {e : ε}

public theorem subst_wk1_lift_cons (b v : Expr (Φ ⊕ Ψ)) (ξ : Nat → Expr (Φ ⊕ Ψ)) :
    b.wk1.subst (Expr.liftSubst (cons v ξ)) = b.subst (Expr.liftSubst ξ) := by
  rw [Expr.wk1, Expr.subst_wk]
  congr 1
  funext i
  cases i <;> rfl

public theorem subst_wk2_lift_cons (b v : Expr (Φ ⊕ Ψ)) (ξ : Nat → Expr (Φ ⊕ Ψ)) :
    b.wk2.subst (Expr.liftSubst (Expr.liftSubst (cons v ξ))) = b.subst (Expr.liftSubst (Expr.liftSubst ξ)) := by
  rw [Expr.wk2, Expr.subst_wk]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

private theorem lift_comp (σ ξ : Nat → Expr (Φ ⊕ Ψ)) :
    (fun i => (Expr.liftSubst σ i).subst (Expr.liftSubst ξ)) =
      Expr.liftSubst (fun i => (σ i).subst ξ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    change (σ i).wk0.subst (Expr.liftSubst ξ) = ((σ i).subst ξ).wk0
    rw [Expr.wk0, Expr.subst_wk, Expr.wk0, Expr.wk_subst]
    rfl

public theorem subst_lift_comp (b : Expr (Φ ⊕ Ψ)) (σ ξ : Nat → Expr (Φ ⊕ Ψ)) :
    (b.subst (Expr.liftSubst σ)).subst (Expr.liftSubst ξ) =
      b.subst (Expr.liftSubst (fun i => (σ i).subst ξ)) := by
  rw [Expr.subst_comp, lift_comp]

public theorem subst_lift2_comp (b : Expr (Φ ⊕ Ψ)) (σ ξ : Nat → Expr (Φ ⊕ Ψ)) :
    (b.subst (Expr.liftSubst (Expr.liftSubst σ))).subst (Expr.liftSubst (Expr.liftSubst ξ)) =
      b.subst (Expr.liftSubst (Expr.liftSubst (fun i => (σ i).subst ξ))) := by
  rw [subst_lift_comp, lift_comp]

public theorem subst_pair_beta (b p q : Expr (Φ ⊕ Ψ)) (σ : Nat → Expr (Φ ⊕ Ψ)) :
    (((b.subst (Expr.liftSubst (Expr.liftSubst σ))).subst (Expr.liftSubst p.subst0)).subst q.subst0) =
      b.subst (cons q (cons p σ)) := by
  rw [subst_lift_comp]
  change (b.subst (Expr.liftSubst (fun i => (Expr.liftSubst σ i).subst (cons p Expr.var)))).subst
    (cons q Expr.var) = _
  rw [subst_lift_cons]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    cases i with
    | zero =>
      change p.subst Expr.var = p
      exact Expr.subst_var _
    | succ i =>
      change (((σ i).wk0.subst (cons p Expr.var)).subst Expr.var) = σ i
      rw [subst_wk0_cons, Expr.subst_var, Expr.subst_var]

public theorem wf_wk2 {b : Expr (Φ ⊕ Ψ)} (x : Ty α)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
          Wf ((B, ⊥) :: (A, ⊥) :: Γ) b C e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf ((B, ⊥) :: (A, ⊥) :: (x, ⊥) :: Γ) b.wk2 C e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  rw [Expr.wk2, Expr.wk_eq_subst]
  apply hb.subst_typed
  intro i
  refine Fin.cases (motive := fun i =>
    Wf ((B, (⊥ : ε)) :: (A, ⊥) :: (x, ⊥) :: Γ)
      (.var (Expr.liftWk (Expr.liftWk Nat.succ) i.val))
      (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get i).1 (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get i).2)
    (.var 0 le_rfl) ?_ i
  intro j
  exact Fin.cases (motive := fun j =>
    Wf ((B, (⊥ : ε)) :: (A, ⊥) :: (x, ⊥) :: Γ)
      (.var (Expr.liftWk (Expr.liftWk Nat.succ) j.succ.val))
      (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get j.succ).1
      (((B, (⊥ : ε)) :: (A, ⊥) :: Γ).get j.succ).2)
    (.var 1 le_rfl) (fun k => Wf.var (Γ := (B, ⊥) :: (A, ⊥) :: (x, ⊥) :: Γ) k.succ.succ.succ le_rfl) j

public theorem let2_bind {a b : Expr (Φ ⊕ Ψ)}
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.product A B) e)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf ((B, ⊥) :: (A, ⊥) :: Γ) b C e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ C e (.let₂ a b) (.let₁ a (.let₂ (.var 0) b.wk2)) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  exact .step (.rewrite (.let₂ ha hb) (.let₁ ha (.let₂ (.var 0 bot_le) (wf_wk2 S T _ hb))) (.let2_bind _ _))

public theorem let2_pure_beta {p q b : Expr (Φ ⊕ Ψ)}
    (hp : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ p A ⊥)
    (hq : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ q B ⊥)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf ((B, ⊥) :: (A, ⊥) :: Γ) b C e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ C e (.let₂ (.pair p q) b) ((b.subst (Expr.liftSubst p.subst0)).subst q.subst0) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hp' := hp.weakenEffect (show (⊥ : ε) ≤ e from bot_le)
  have hq' := hq.weakenEffect (show (⊥ : ε) ≤ e from bot_le)
  have hqwk := CallByValue.wf_wk0 hq' (A, ⊥)
  have hstep := Eqv.step (Step.rewrite (.let₂ (.pair hp' hq') hb)
    (.let₁ hp' (.let₁ hqwk hb)) (Rewrite.let2_pair p q b))
  have hbeta := Eqv.step (Step.let1_beta hp (.let₁ hqwk hb))
  change Eqv Γ C e (.let₁ p (.let₁ q.wk0 b))
    (.let₁ (q.wk0.subst (cons p Expr.var)) (b.subst (Expr.liftSubst p.subst0))) at hbeta
  rw [subst_wk0_cons, Expr.subst_var] at hbeta
  have hsub : ∀ i : Fin ((A, (⊥ : ε)) :: Γ).length, Wf Γ (p.subst0 i.val)
      (((A, (⊥ : ε)) :: Γ).get i).1 (((A, (⊥ : ε)) :: Γ).get i).2 :=
    fun i => Fin.cases (motive := fun i => Wf Γ (p.subst0 i.val)
      (((A, (⊥ : ε)) :: Γ).get i).1 (((A, (⊥ : ε)) :: Γ).get i).2) hp (fun j => .var j le_rfl) i
  exact hstep.trans (hbeta.trans (.step (.let1_beta hq (hb.subst_typed (typed_lift S T hsub (B, ⊥))))))

public theorem case_bind {a l r : Expr (Φ ⊕ Ψ)}
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a (.coprod A B) e)
    (hl : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf ((A, ⊥) :: Γ) l C e)
    (hr : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf ((B, ⊥) :: Γ) r C e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ C e (.case a l r) (.let₁ a (.case (.var 0) l.wk1 r.wk1)) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  exact .step (.rewrite (.case ha hl hr)
    (.let₁ ha (.case (.var 0 bot_le) (wf_wk1 S T (.coprod A B) hl) (wf_wk1 S T (.coprod A B) hr)))
    (.case_bind _ _ _))

public theorem inl_bind {a : Expr (Φ ⊕ Ψ)}
    (ha : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ a A e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.coprod A B) e (.inl a) (.let₁ a (.inl (.var 0))) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hv : Wf Γ (.inl a) (Ty.coprod A B) e := .inl ha
  have hl : Wf ((A, ⊥) :: Γ) (.inl (.var 0) : Expr (Φ ⊕ Ψ)) (Ty.coprod A B) e := .inl (.var 0 bot_le)
  have hr : Wf ((B, ⊥) :: Γ) (.inr (.var 0) : Expr (Φ ⊕ Ψ)) (Ty.coprod A B) e := .inr (.var 0 bot_le)
  have hw := Wf.case hv hl hr
  exact (Eqv.step (.rewrite hw hv (.case_eta _))).symm.trans
    (.step (.reduce hw (.let₁ ha hl) (.case_inl _ _ _)))

public theorem inr_bind {b : Expr (Φ ⊕ Ψ)}
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Wf Γ b B e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Eqv Γ (.coprod A B) e (.inr b) (.let₁ b (.inr (.var 0))) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  have hv : Wf Γ (.inr b) (Ty.coprod A B) e := .inr hb
  have hl : Wf ((A, ⊥) :: Γ) (.inl (.var 0) : Expr (Φ ⊕ Ψ)) (Ty.coprod A B) e := .inl (.var 0 bot_le)
  have hr : Wf ((B, ⊥) :: Γ) (.inr (.var 0) : Expr (Φ ⊕ Ψ)) (Ty.coprod A B) e := .inr (.var 0 bot_le)
  have hw := Wf.case hv hl hr
  exact (Eqv.step (.rewrite hw hv (.case_eta _))).symm.trans
    (.step (.reduce hw (.let₁ hb hr) (.case_inr _ _ _)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs
