module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.EffectWeakening.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  {Γ : EffectCtx (Ty α) ε} {A : Ty α} {a b : Expr Φ} {e lo hi : ε}

theorem case_raw_wf [Preorder ε] [OrderBot ε] (h : CaseRaw e Γ A a) : Wf Γ a A e := by
  induction h with
  | straight raw =>
      obtain ⟨_, eq, _⟩ := raw.normalize
      exact eq.endpoints_wf.1
  | bind _ _ ih₁ ih₂ => exact .let₁ ih₁ ih₂
  | branch _ _ _ ih₁ ih₂ ih₃ => exact .case ih₁ ih₂ ih₃
  | call _ bound _ ih => exact .op bound ih
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | let2 _ _ ih₁ ih₂ => exact .let₂ ih₁ ih₂

theorem written_weaken [Preorder ε] [OrderBot ε]
    (h : ReplyReflection.Written A e Γ a) (hle : e ≤ hi) :
    ReplyReflection.Written A hi Γ a := by
  induction h with
  | leaf eq typed leaf => exact .leaf (eqv_weakenEffect eq hle) typed leaf
  | call eq visible bound typed leaf hk _ ih =>
      exact .call (eqv_weakenEffect eq hle) visible (bound.trans hle) typed leaf (hk.weakenEffect hle) ih

variable [SemilatticeSup ε] [OrderBot ε]

theorem instructionBound_le (h : Wf Γ a A e) : instructionBound a ≤ e := by
  induction h with
  | var _ _ | unit _ _ => exact bot_le
  | op bound _ ih => exact sup_le bound ih
  | pair _ _ ih₁ ih₂ | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ => exact sup_le ih₁ ih₂
  | case _ _ _ ih₁ ih₂ ih₃ => exact sup_le ih₁ (sup_le ih₂ ih₃)
  | inl _ ih | inr _ ih | abort _ ih => exact ih

private theorem raw_at_bound (h : Raw e Γ A a) (bound : instructionBound a ≤ lo) :
    Raw lo Γ A a := by
  induction h with
  | leaf typed leaf => exact .leaf typed leaf
  | call visible _ _ ih => exact .call visible (le_sup_left.trans bound) (ih (le_sup_right.trans bound))
  | let1 _ _ ih₁ ih₂ => exact .let1 (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_right.trans bound))
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_right.trans bound))

theorem case_raw_at_bound (h : CaseRaw e Γ A a) (bound : instructionBound a ≤ lo) :
    CaseRaw lo Γ A a := by
  induction h with
  | straight raw => exact .straight (raw_at_bound raw bound)
  | bind _ _ ih₁ ih₂ => exact .bind (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_right.trans bound))
  | branch _ _ _ ih₁ ih₂ ih₃ =>
      have arms := le_sup_right.trans bound
      exact .branch (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_left.trans arms)) (ih₃ (le_sup_right.trans arms))
  | call visible _ _ ih => exact .call visible (le_sup_left.trans bound) (ih (le_sup_right.trans bound))
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_right.trans bound))
  | let2 _ _ ih₁ ih₂ => exact .let2 (ih₁ (le_sup_left.trans bound)) (ih₂ (le_sup_right.trans bound))

variable [DecidableEq α] [EffectIteration ε]

theorem packed_weaken_eq_iff_at
    (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
    {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {ea eb : ε} (a : TypedExpr Φ Γ A ea) (b : TypedExpr Φ Γ A eb)
    (left : CaseRaw lo Γ A a.val) (right : CaseRaw lo Γ A b.val)
    (ha : ea ≤ hi) (hb : eb ≤ hi) (hle : lo ≤ hi) :
    weakenEffect ha (denote a) = weakenEffect hb (denote b) ↔ Eqv Γ A lo a.val b.val := by
  let aHi : TypedExpr Φ Γ A hi := ⟨a.val, a.prop.weakenEffect ha⟩
  let bHi : TypedExpr Φ Γ A hi := ⟨b.val, b.prop.weakenEffect hb⟩
  change denote aHi = denote bHi ↔ Eqv Γ A lo a.val b.val
  rw [denote_eq_iff_eqv hΓ aHi bHi]
  constructor
  · intro eq
    obtain ⟨t, ht, _⟩ := a.prop.toLetIter
    obtain ⟨s, hs', _⟩ := b.prop.toLetIter
    exact (case_reflection profile hΓ hs left right ht hs').mp (eq.toLetIter ht hs')
  · exact fun eq => eqv_weakenEffect eq hle

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs
