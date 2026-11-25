module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection

/-! # Pure endpoint reflection in recursively split product and sum contexts -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection

universe u w

variable {α Φ : Type u} (S : FreeTree.Signature α Φ)
  {ε : Type w} [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  [DecidableEq α]

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
  Proofs.endpoint_reflection S hΓ hInput e ha hb ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection
