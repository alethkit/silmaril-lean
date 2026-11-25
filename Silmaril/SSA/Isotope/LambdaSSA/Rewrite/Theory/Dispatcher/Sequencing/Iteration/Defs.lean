module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Defs

/-! # Iteration with explicit linked dispatch -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v}

/-- Route the sum exit through a CFG block. The branch payload is evaluated
before the return-or-repeat decoder sees it. -/
def linkedIterationBody (A B : τ) (step : Region Φ) : Region Φ :=
  step.linkExits [Silmaril.coprod B A] (fun _ => SyntacticCategory.iterationDispatch)

/-- Run one-local-label feedback with the linked decoder in the body. -/
def linkedIterate (A B : τ) (step : Region Φ) : Region Φ :=
  feedbackRegion [A] (fun _ => linkedIterationBody A B step) 0

/-- Run the step and link its output to the case that returns or repeats.
The repeat arm drops the original state and the decoded sum slot. -/
def linkedFixpointRhs (A B : τ) (step : Region Φ) : Region Φ :=
  step.linkExits [Silmaril.coprod B A] (fun _ =>
    .case (.var 0) (.br 0 (.var 0)) ((linkedIterate A B step).renameVars (lift (Nat.succ ∘ Nat.succ))))

end Silmaril.Isotope.LambdaSSA.Region
