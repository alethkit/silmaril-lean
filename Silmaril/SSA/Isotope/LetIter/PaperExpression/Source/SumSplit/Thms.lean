module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit

/-! # Typed sum specialization and reconstruction at the original effect bound -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit

universe u v w

variable {τ : Type u} {Φ : Type v} {ε : Type w}

section Source

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
variable {Γ : EffectCtx τ ε} {A B C X : τ} {e : ε} {a b : Expr Φ}

omit [TypeFormers τ] in
/-- Replacing one slot by a bottom-annotated payload preserves purity of the context. -/
theorem branchCtx_pure (hΓ : Γ.Pure) (i : Fin Γ.length) (X : τ) :
    (branchCtx Γ i X).Pure :=
  Proofs.branchCtx_pure hΓ i X

/-- Each injection specialization keeps the same result type and effect bound. -/
theorem wf_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Wf (branchCtx Γ i A) (left i a) C e ∧ Wf (branchCtx Γ i B) (right i a) C e :=
  Proofs.wf_specializations i ht he ha

/-- Rebuild an expression by casing on a pure sum slot and weakening its specializations. -/
theorem eqv_rebuild (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) :
    Eqv Γ C e a (rebuild i a) :=
  Proofs.eqv_rebuild i ht he ha

/-- The two injection specializations characterize source equality at the same bound. -/
theorem eqv_iff_specializations (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (ha : Wf Γ a C e) (hb : Wf Γ b C e) :
    Eqv Γ C e a b ↔
      Eqv (branchCtx Γ i A) C e (left i a) (left i b) ∧
      Eqv (branchCtx Γ i B) C e (right i a) (right i b) :=
  Proofs.eqv_iff_specializations i ht he ha hb

section CaseArms

variable {l r l' r' : Expr Φ}

/-- Build a typed case from programs in the two specialized contexts. -/
theorem caseArms_wf (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Wf Γ (caseArms i l r) C e :=
  Proofs.caseArms_wf i ht he hl hr

/-- The left injection of a free payload exposes the left program. -/
theorem caseArms_left (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Eqv (branchCtx Γ i A) C e (left i (caseArms i l r)) l :=
  Proofs.caseArms_left i ht he hl hr

/-- The right injection of a free payload exposes the right program. -/
theorem caseArms_right (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥) (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e) :
    Eqv (branchCtx Γ i B) C e (right i (caseArms i l r)) r :=
  Proofs.caseArms_right i ht he hl hr

/-- Case equality at the selected slot is exactly equality of both arms at the supplied bound. -/
theorem caseArms_eqv_iff (i : Fin Γ.length) (ht : (Γ.get i).1 = coprod A B)
    (he : (Γ.get i).2 = ⊥)
    (hl : Wf (branchCtx Γ i A) l C e) (hr : Wf (branchCtx Γ i B) r C e)
    (hl' : Wf (branchCtx Γ i A) l' C e) (hr' : Wf (branchCtx Γ i B) r' C e) :
    Eqv Γ C e (caseArms i l r) (caseArms i l' r') ↔
      Eqv (branchCtx Γ i A) C e l l' ∧ Eqv (branchCtx Γ i B) C e r r' :=
  Proofs.caseArms_eqv_iff i ht he hl hr hl' hr'

end CaseArms

end Source

section Native

variable [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}

/-- A native equality transports through both pure sum-slot substitutions. -/
theorem native_specializations {X Y Z : τ} (i : Fin Γ.length) (hΓ : Γ.Pure)
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
  Proofs.native_specializations i hΓ hi ht hs hn

end Native

end Silmaril.Isotope.LetIter.PaperExpression.Source.SumSplit
