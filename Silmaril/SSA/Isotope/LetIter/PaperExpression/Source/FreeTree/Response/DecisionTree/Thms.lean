module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Flatten.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree

/-! # Original-bound reflection for matched pure-input decision trees -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree

universe u w

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {shape : Shape Γ} {c : α}

/-- The rendered decisions and all their straight-line leaves type-check
at the supplied bound. -/
theorem source_wf (hΓ : Γ.Pure) (e : ε)
    (p : Program S c shape) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    Wf Γ p.source (.base c) e :=
  Proofs.source_wf S hΓ e p hp

variable [EffectIteration ε] [DecidableEq α]

/-- Reflect native equality of two decision trees with the same tested slots
and nesting. Every split tests a pure input sum with atomic payloads. The
native proof may use arbitrary well-typed intermediates. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (e : ε)
    (p q : Program S c shape) (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S hΓ e p q hp hq ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree
