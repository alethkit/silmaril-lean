module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder

/-! # Original-bound reflection across different pure-input decision tree orders -/

public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder

universe u w

variable {α Φ : Type u} (S : Signature α Φ) {ε : Type w}
  [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ : EffectCtx (Ty α) ε} {c : α}

/-- Choose any full split shape for the same context. Specializing the program
along each path selects its straight-line leaf, and reconstruction gives an
equivalent program in the chosen shape at the original bound. -/
theorem normalize_to (hΓ : Γ.Pure) (e : ε) (target : Shape Γ)
    {shape : Shape Γ} (p : Program S c shape) (hp : Program.WellTyped S e p) :
    letI := S.endpoints
    ∃ q : Program S c target, Program.WellTyped S e q ∧ Eqv Γ (.base c) e p.source q.source :=
  Proofs.normalize_to S hΓ e target p hp

variable [EffectIteration ε] [DecidableEq α]

/-- Pure sum tests with atomic payloads may occur in different orders on
either side. Source equality stays at the supplied bound. The native proof
may use arbitrary well-typed intermediates. -/
theorem endpoint_reflection (hΓ : Γ.Pure) (e : ε) {shape other : Shape Γ}
    (p : Program S c shape) (q : Program S c other)
    (hp : Program.WellTyped S e p) (hq : Program.WellTyped S e q)
    {t s : Tm Empty Φ Γ.length}
    (ht : p.source.toLetIter Γ.length = some t) (hs : q.source.toLetIter Γ.length = some s) :
    letI := S.endpoints
    AbortEquiv (⊥ : ε) (.nil : Ctx Empty (Ty α)) Γ.toBoundCtx t s (.base c) ↔
      Eqv Γ (.base c) e p.source q.source :=
  Proofs.endpoint_reflection S hΓ e p q hp hq ht hs

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.DecisionTree.Reorder
