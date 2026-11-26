module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.EffectWeakening.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.EffectWeakening.Weakening

/-! # Effect weakening for packed finite branching expressions -/

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (Profile)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε]
  {Γ : EffectCtx (Ty α) ε} {A : Ty α} {a : Expr Φ} {e lo hi : ε}

theorem CaseRaw.wf [Preorder ε] [OrderBot ε] (h : CaseRaw e Γ A a) : Wf Γ a A e :=
  Proofs.case_raw_wf h

/-- Transport an existing normalization witness with the same exposed
requests, arguments and reply specializations. -/
theorem written_weaken [Preorder ε] [OrderBot ε]
    (h : ReplyReflection.Written A e Γ a) (hle : e ≤ hi) :
    ReplyReflection.Written A hi Γ a :=
  Proofs.written_weaken h hle

variable [SemilatticeSup ε] [OrderBot ε]

theorem instructionBound_le (h : Wf Γ a A e) : instructionBound a ≤ e :=
  Proofs.instructionBound_le h

/-- For a recognized endpoint, the join of the instruction effects is the
least bound. Rescoping the bound keeps the same syntax and constructor types. -/
theorem CaseRaw.at_bound_iff (h : CaseRaw e Γ A a) :
    CaseRaw lo Γ A a ↔ instructionBound a ≤ lo :=
  ⟨fun d => instructionBound_le d.wf, Proofs.case_raw_at_bound h⟩

theorem CaseRaw.weakenEffect (h : CaseRaw e Γ A a) (hle : e ≤ hi) : CaseRaw hi Γ A a :=
  h.at_bound_iff.mpr ((instructionBound_le h.wf).trans hle)

variable [DecidableEq α] [EffectIteration ε]
  (profile : Profile (α := α) Φ ε) (hΓ : Γ.Pure)
  {slots : Fin Γ.length → α} (hs : ∀ i, (Γ.get i).1 = .base (slots i))
include profile hΓ hs

/-- The packed hom can compare different presentations of the two endpoints.
Reflection holds at a shared bound admitting both raw derivations. -/
theorem packed_weaken_eq_iff_at {ea eb : ε} (a : TypedExpr Φ Γ A ea) (b : TypedExpr Φ Γ A eb)
    (left : CaseRaw lo Γ A a.val) (right : CaseRaw lo Γ A b.val)
    (ha : ea ≤ hi) (hb : eb ≤ hi) (hle : lo ≤ hi) :
    weakenEffect ha (denote a) = weakenEffect hb (denote b) ↔ Eqv Γ A lo a.val b.val :=
  Proofs.packed_weaken_eq_iff_at profile hΓ hs a b left right ha hb hle

/-- Independently bounded raw endpoints reflect from the common larger hom
at the join of their original bounds. -/
theorem packed_weaken_eq_iff_join {ea eb : ε} (a : TypedExpr Φ Γ A ea) (b : TypedExpr Φ Γ A eb)
    (left : CaseRaw ea Γ A a.val) (right : CaseRaw eb Γ A b.val)
    (ha : ea ≤ hi) (hb : eb ≤ hi) :
    weakenEffect ha (denote a) = weakenEffect hb (denote b) ↔ Eqv Γ A (ea ⊔ eb) a.val b.val :=
  packed_weaken_eq_iff_at profile hΓ hs a b
    (left.weakenEffect le_sup_left) (right.weakenEffect le_sup_right) ha hb (sup_le ha hb)

/-- Weakening the packed hom reflects equality on the image of finite
`CaseRaw` representatives at the lower bound. -/
theorem packed_weakening_injOn_caseRaw_image (hle : lo ≤ hi) :
    Set.InjOn (weakenEffect (Γ := [(packType Γ, ⊥)]) (A := A) (Φ := Φ) hle)
      {f | ∃ a : TypedExpr Φ Γ A lo, CaseRaw lo Γ A a.val ∧ denote a = f} := by
  rintro _ ⟨a, left, rfl⟩ _ ⟨b, right, rfl⟩ eq
  exact (denote_eq_iff_eqv hΓ a b).mpr
    ((packed_weaken_eq_iff_at profile hΓ hs a b left right hle hle hle).mp eq)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments
