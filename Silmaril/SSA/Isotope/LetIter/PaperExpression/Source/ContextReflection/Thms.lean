module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection

/-! # Pure endpoint reflection in recursively split finite pure contexts -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection

universe u v w

section Cover

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]

/-- Transport reflection through the recursive cover by pure atomic contexts. -/
theorem reflect_of_atomic (lo e : ε) (hle : lo ≤ e) {C : Ty α}
    (atomic : ∀ {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
      {a b : Expr Φ} {t s : Tm Empty Φ Γ.length},
      Γ.Pure → (∀ i, (Γ.get i).1 = .base (slots i)) →
      Wf Γ a C lo → Wf Γ b C lo →
      a.toLetIter Γ.length = some t → b.toLetIter Γ.length = some s →
      AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C →
      Eqv Γ C e a b)
    {Γ : EffectCtx (Ty α) ε} {a b : Expr Φ} {t s : Tm Empty Φ Γ.length}
    (hΓ : Γ.Pure) (ha : Wf Γ a C lo) (hb : Wf Γ b C lo)
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s)
    (hn : AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C) :
    Eqv Γ C e a b :=
  Proofs.reflect_of_atomic lo e hle atomic hΓ ha hb ht hs hn

end Cover

variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α]

/-- Reflect arbitrary native equality between bottom-typed source endpoints
at any result type. The finite pure context may contain any source type, and the
source equation retains the supplied effect bound. -/
theorem endpoint_reflection_all_contexts {Γ : EffectCtx (Ty α) ε} {C : Ty α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a C (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b C (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C ↔
      Eqv Γ C e a b :=
  Proofs.endpoint_reflection_all_contexts S hΓ e ha hb ht hs

-- Keep the original named argument for callers of the product/sum result.
set_option linter.unusedVariables false in
/-- Reflect arbitrary native equality between bottom-typed source endpoints
at any result type. Each ambient slot is generated from atoms by binary
products and sums, and the source equation retains the supplied effect bound. -/
theorem endpoint_reflection_all_results {Γ : EffectCtx (Ty α) ε} {C : Ty α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (hInput : ∀ i : Fin Γ.length, InputType (Γ.get i).1) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a C (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b C (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s C ↔
      Eqv Γ C e a b :=
  endpoint_reflection_all_contexts S hΓ e ha hb ht hs

/-- Reflect arbitrary native equality between bottom-typed source endpoints
with atomic result. Each ambient slot is generated from atoms by binary
products and sums, and the source equation retains the supplied effect bound. -/
theorem endpoint_reflection {Γ : EffectCtx (Ty α) ε} {C : α} {a b : Expr Φ}
    (hΓ : Γ.Pure) (hInput : ∀ i : Fin Γ.length, InputType (Γ.get i).1) (e : ε)
    (ha : letI := S.endpoints; Wf Γ a (.base C) (⊥ : ε))
    (hb : letI := S.endpoints; Wf Γ b (.base C) (⊥ : ε))
    {t s : Tm Empty Φ Γ.length}
    (ht : a.toLetIter Γ.length = some t) (hs : b.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base C) ↔
      Eqv Γ (.base C) e a b :=
  endpoint_reflection_all_results S hΓ hInput e ha hb ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection
