module

public import Silmaril.Logic.Temporal.TLA.Defs

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Rules.Figure5

universe u

/-- Classical propositional natural deduction in the `¬, ∧` basis. A TLA formula
can be used as an opaque proposition. Only the propositional rules below inspect
its connectives. The context supplies previously established formulas for STL1. -/
inductive PropDerives {S : Type u} : List (Formula S) → Formula S → Prop where
  | hyp {Γ F} : F ∈ Γ → PropDerives Γ F
  | conjIntro {Γ F G} : PropDerives Γ F → PropDerives Γ G → PropDerives Γ (.conj F G)
  | conjLeft {Γ F G} : PropDerives Γ (.conj F G) → PropDerives Γ F
  | conjRight {Γ F G} : PropDerives Γ (.conj F G) → PropDerives Γ G
  | negIntro {Γ F G} : PropDerives (F :: Γ) G → PropDerives (F :: Γ) (.neg G) →
      PropDerives Γ (.neg F)
  | reductio {Γ F G} : PropDerives (.neg F :: Γ) G → PropDerives (.neg F :: Γ) (.neg G) →
      PropDerives Γ F

end Silmaril.Logic.Temporal.TLA.Rules.Figure5
