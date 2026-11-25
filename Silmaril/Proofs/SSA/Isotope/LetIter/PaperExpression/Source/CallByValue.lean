module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms

/-! # Derived call-by-value conversions for source expressions -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.CallByValue.Proofs

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ : EffectCtx τ ε} {A B : τ} {e : ε} {a b : Expr Φ}

public theorem wf_wk0 (hb : Wf Γ b B e) (slot : τ × ε) :
    Wf (slot :: Γ) b.wk0 B e := by
  rw [Expr.wk0, Expr.wk_eq_subst]
  exact hb.subst_typed (σ := Expr.var ∘ Nat.succ)
    fun i => Wf.var (Γ := slot :: Γ) i.succ le_rfl

public theorem op_bind {f : Φ} (hf : instrEff f ≤ e) (ha : Wf Γ a (instrSrc f) e) :
    Eqv Γ (instrTrg f) e (.op f a) (.let₁ a (.op f (.var 0))) := by
  have ht := Wf.op (f := f) hf ha
  have hv : Wf ((instrSrc f, (⊥ : ε)) :: Γ) (.op f (.var 0)) (instrTrg f) e :=
    .op hf (.var 0 bot_le)
  have heta := Eqv.step (Step.rewrite (.let₁ ht (.var 0 bot_le)) ht (.let1_eta _))
  have hsplit : Eqv Γ (instrTrg f) e (.let₁ (.op f a) (.var 0))
      (.let₁ a (.let₁ (.op f (.var 0)) (.var 0))) :=
    .step (.rewrite (.let₁ ht (.var 0 bot_le))
      (.let₁ ha (.let₁ hv (.var 0 bot_le))) (.let1_op _ _ _))
  exact heta.symm.trans (hsplit.trans
    (.let1 (.refl ha) (.step (.rewrite (.let₁ hv (.var 0 bot_le)) hv (.let1_eta _)))))

public theorem op_let {f : Φ} (hf : instrEff f ≤ e) (ha : Wf Γ a A e)
    (hb : Wf ((A, ⊥) :: Γ) b (instrSrc f) e) :
    Eqv Γ (instrTrg f) e (.op f (.let₁ a b)) (.let₁ a (.op f b)) := by
  have hv : Wf ((instrSrc f, (⊥ : ε)) :: Γ) (.op f (.var 0)) (instrTrg f) e :=
    .op hf (.var 0 bot_le)
  have hv' : Wf ((instrSrc f, (⊥ : ε)) :: (A, ⊥) :: Γ) (.op f (.var 0)) (instrTrg f) e :=
    .op hf (.var 0 bot_le)
  have hsplit : Eqv Γ (instrTrg f) e (.let₁ (.let₁ a b) (.op f (.var 0)))
      (.let₁ a (.let₁ b (.op f (.var 0)))) :=
    .step (.rewrite (.let₁ (.let₁ ha hb) hv) (.let₁ ha (.let₁ hb hv')) (.let1_let1 _ _ _))
  exact (op_bind hf (.let₁ ha hb)).trans
    (hsplit.trans (.let1 (.refl ha) (op_bind hf hb).symm))

/-- Pairs evaluate their first component before the second. -/
public theorem pair_bind (ha : Wf Γ a A e) (hb : Wf Γ b B e) :
    Eqv Γ (product A B) e (.pair a b)
      (.let₁ a (.let₁ b.wk0 (.pair (.var 1) (.var 0)))) := by
  have hpair := Wf.pair ha hb
  have hvars : Wf ((B, (⊥ : ε)) :: (A, ⊥) :: Γ) (.pair (.var 1) (.var 0) : Expr Φ)
      (product A B) e := .pair (.var 1 bot_le) (.var 0 bot_le)
  have hx := Wf.let₂ hpair hvars
  exact (Eqv.step (.rewrite hx hpair (.let2_eta _))).symm.trans
    (.step (.rewrite hx (.let₁ ha (.let₁ (wf_wk0 hb (A, ⊥)) hvars)) (.let2_pair _ _ _)))

public theorem pair_unit_bind (ha : Wf Γ a A e) :
    Eqv Γ (product A (unit : τ)) e (.pair a .unit)
      (.let₁ a (.pair (.var 0) .unit)) := by
  have hv : Wf (((unit : τ), (⊥ : ε)) :: (A, ⊥) :: Γ) (.pair (.var 1) (.var 0) : Expr Φ)
      (product A (unit : τ)) e := .pair (.var 1 bot_le) (.var 0 bot_le)
  have hb := Eqv.step (Step.let1_beta (Wf.unit ((A, ⊥) :: Γ) (⊥ : ε)) hv)
  exact (pair_bind ha (.unit Γ e)).trans (.let1 (.refl ha) hb)

/-- A binary input tuple evaluates the left component before the right. -/
public theorem pair_two_bind (ha : Wf Γ a A e) (hb : Wf Γ b B e) :
    Eqv Γ (product A (product B (unit : τ))) e (.pair a (.pair b .unit))
      (.let₁ a (.let₁ b.wk0 (.pair (.var 1) (.pair (.var 0) .unit)))) := by
  let X := product B (unit : τ)
  let Δ := (A, (⊥ : ε)) :: Γ
  have hb₀ := wf_wk0 hb (A, ⊥)
  have hxy : Wf ((X, (⊥ : ε)) :: Δ) (.pair (.var 1) (.var 0) : Expr Φ) (product A X) e :=
    .pair (.var 1 bot_le) (.var 0 bot_le)
  have hxy' : Wf ((X, (⊥ : ε)) :: (B, ⊥) :: Δ) (.pair (.var 2) (.var 0) : Expr Φ)
      (product A X) e := .pair (.var 2 bot_le) (.var 0 bot_le)
  have htuple : Wf ((B, (⊥ : ε)) :: Δ) (.pair (.var 0) .unit : Expr Φ) X (⊥ : ε) :=
    .pair (.var 0 le_rfl) (.unit _ _)
  have htupleE : Wf ((B, (⊥ : ε)) :: Δ) (.pair (.var 0) .unit : Expr Φ) X e :=
    .pair (.var 0 bot_le) (.unit _ _)
  have h0 := pair_bind ha (Wf.pair hb (.unit Γ e))
  have h1 := Eqv.let1 (pair_unit_bind hb₀) (.refl hxy)
  have h2 : Eqv Δ (product A X) e
      (.let₁ (.let₁ b.wk0 (.pair (.var 0) .unit)) (.pair (.var 1) (.var 0)))
      (.let₁ b.wk0 (.let₁ (.pair (.var 0) .unit) (.pair (.var 2) (.var 0)))) :=
    .step (.rewrite (.let₁ (.let₁ hb₀ htupleE) hxy)
      (.let₁ hb₀ (.let₁ htupleE hxy')) (.let1_let1 _ _ _))
  have h3 := Eqv.let1 (.refl hb₀) (.step (.let1_beta htuple hxy'))
  exact h0.trans (.let1 (.refl ha) (h1.trans (h2.trans h3)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.CallByValue.Proofs
