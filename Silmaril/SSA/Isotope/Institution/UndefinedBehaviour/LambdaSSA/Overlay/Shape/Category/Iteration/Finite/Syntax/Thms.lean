module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Adequacy

/-! # Complete shaped observations from executable typed steps -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax

universe u

variable {Φ : Type u} [HasTy Φ Ty] {states : Nat} {Γ : List Ty}
variable {X A B : Ty} {captures seeds results : Nat}

/-- Structural evaluation gives the complete shaped observation of the
elaborated overlay region. A reply binds at its final machine state. -/
theorem observe_eval (prim : Primitives Φ states) (body : Program Φ Γ A)
    (env : Bindings Γ) (s : Fin states) :
    Shape.denote body.region (model prim env) s = (body.eval prim env s).behaviour :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.observe_eval prim body env s

/-- The generated rows certify the actual typed overlay step at all coded
capture, seed and initial state combinations. -/
theorem generate_certified (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (body : Program Φ [A, X] (.coprod B A)) :
    Certified (codes.carrier prim) body.region (generate codes prim body) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.generate_certified codes prim body

/-- Comparing the generated tables decides pointwise shaped refinement of
the actual captured overlay loops at every supported start. -/
theorem check_generate_iff (codes : Codes X A B captures seeds results) (prim : Primitives Φ states)
    (lower upper : Program Φ [A, X] (.coprod B A)) :
    check (generate codes prim lower) (generate codes prim upper) = true ↔
      ∀ (c : Fin captures) (a : Payload A) (s : Fin states),
        (iterateCaptured (model prim emptyBindings) lower.region).run 0
          (pairPayload (codes.capture c) a) s ≤
        (iterateCaptured (model prim emptyBindings) upper.region).run 0
          (pairPayload (codes.capture c) a) s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax.check_generate_iff
    codes prim lower upper

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
