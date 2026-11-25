module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Equations
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.Substitution

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTagProofs

open KnownTag (injection residual)
open Proofs (TypedSubst Renaming wf_subst wf_wk eqv_typed subst0_subst)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ Δ : EffectCtx τ ε} {A B C X : τ} {e : ε}
  {s s' p l r : Expr Φ} {tag tag' : Sum (Expr Φ) (Expr Φ)}

theorem payload_wf (h : KnownTag Γ A B e s tag) :
    tag.elim (fun p => Wf Γ p A e) (fun p => Wf Γ p B e) := by
  induction h with
  | inl h | inr h => exact h
  | letPure _ _ _ ih => exact ih

private theorem subst {σ : Nat → Expr Φ} (h : KnownTag Γ A B e s tag)
    (hs : TypedSubst Δ Γ σ) :
    KnownTag Δ A B e (s.subst σ) (tag.map (Expr.subst σ) (Expr.subst σ)) := by
  induction h generalizing Δ σ with
  | inl h => exact .inl (wf_subst h hs)
  | inr h => exact .inr (wf_subst h hs)
  | letPure ha hb _ ih =>
    exact .letPure (wf_subst ha hs) (wf_subst hb (hs.lift (_, ⊥)))
      (subst0_subst _ _ _ ▸ ih hs)

theorem subst0 (h : KnownTag ((X, ⊥) :: Γ) A B e s tag) (hp : Wf Γ p X ⊥) :
    KnownTag Γ A B e (s.subst p.subst0) (tag.map (Expr.subst p.subst0) (Expr.subst p.subst0)) :=
  subst h (TypedSubst.subst0 hp)

theorem unique (h : KnownTag Γ A B e s tag) (h' : KnownTag Γ A B e s tag') : tag = tag' := by
  induction h generalizing tag' with
  | inl _ => cases h'; rfl
  | inr _ => cases h'; rfl
  | letPure _ _ _ ih =>
    cases h' with
    | letPure _ _ ht => exact ih ht

theorem eqv_injection (h : KnownTag Γ A B e s tag) :
    Eqv Γ (coprod A B) e s (injection tag) := by
  induction h with
  | inl h => exact .refl (.inl h)
  | inr h => exact .refl (.inr h)
  | letPure ha hb _ ih => exact (Eqv.step (.let1_beta ha hb)).trans ih

theorem case_eqv (h : KnownTag Γ A B e s tag)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.case s l r) (residual tag l r) := by
  have hc := Eqv.case (eqv_injection h) (.refl hl) (.refl hr)
  cases tag with
  | inl p =>
    have hp := payload_wf h
    exact hc.trans (.step (.reduce (.case (.inl hp) hl hr) (.let₁ hp hl) (.case_inl p l r)))
  | inr p =>
    have hp := payload_wf h
    exact hc.trans (.step (.reduce (.case (.inr hp) hl hr) (.let₁ hp hr) (.case_inr p l r)))

theorem bindCase_eqv (h : KnownTag Γ A B e s tag)
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (.let₁ s (.case (.var 0) l.wk1 r.wk1)) (residual tag l r) := by
  have hs := (eqv_typed (eqv_injection h)).1
  have wk := Renaming.wk0 Γ (coprod A B, ⊥)
  have hb := Wf.case (Wf.var (Γ := (coprod A B, ⊥) :: Γ) 0 (bot_le (a := e)))
    (wf_wk hl (wk.lift (A, ⊥))) (wf_wk hr (wk.lift (B, ⊥)))
  have hbind := Eqv.step (.rewrite (.case hs hl hr) (.let₁ hs hb) (.case_bind s l r))
  exact hbind.symm.trans (case_eqv h hl hr)

theorem residual_eqv (h : KnownTag Γ A B e s tag) (h' : KnownTag Γ A B e s' tag')
    (heq : Eqv Γ (coprod A B) e s s')
    (hl : Wf ((A, ⊥) :: Γ) l C e) (hr : Wf ((B, ⊥) :: Γ) r C e) :
    Eqv Γ C e (residual tag l r) (residual tag' l r) :=
  (case_eqv h hl hr).symm.trans ((Eqv.case heq (.refl hl) (.refl hr)).trans (case_eqv h' hl hr))

end Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTagProofs
