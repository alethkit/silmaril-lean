module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Feedback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Defs

/-! # Typed CFG iteration on native LambdaSSA type arrows -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory

open CategoryTheory

/-- Send a return payload outward and a repeat payload to the local label.
The matched value is the newest variable. -/
@[expose] def iterationDispatch {Φ : Type v} : Region Φ :=
  .case (.var 0) (.br 1 (.var 0)) (.br 0 (.var 0))

/-- Substitute the dispatcher at the step's singleton sum exit. -/
@[expose] def iterationBody {Φ : Type v} (r : Region Φ) : Region Φ :=
  r.lsubst (fun _ => iterationDispatch)

/-- Enter the loop with the newest variable as the initial state. -/
@[expose] def iterateRegion {τ : Type u} {Φ : Type v} (A : τ) (r : Region Φ) : Region Φ :=
  feedbackRegion [A] (fun _ => iterationBody r) 0

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The dispatcher targets the repeat label followed by the return label. -/
theorem iterationDispatch_valueBranches (A B : τ) :
    ValueBranches (Silmaril.coprod B A :: Γ) (iterationDispatch : Region Φ) [A, B] :=
  .case (A := B) (B := A) (.var (i := 0) rfl)
    (.br (ℓ := 1) rfl (.var (i := 0) rfl)) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- Route the two summands into the chosen feedback interface. -/
@[expose] def iterationDispatchHom (A B : τ) :
    (ContinuationContext.single (Silmaril.coprod B A) : ContinuationContext Φ Γ) ⟶
      (ContinuationContext.single A).append (ContinuationContext.single B) :=
  ContinuationContext.singletonToHom (iterationDispatch_valueBranches A B)

/-- Turn an arrow to the sum type into a one-label CFG loop. Its left
summand returns the result and its right summand supplies the next state. -/
@[expose] def iterate {A B : τ} (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType (Silmaril.coprod B A)) :
    ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType B :=
  InducedCategory.homMk (ContinuationContext.feedback (f.hom ≫ iterationDispatchHom A B))

end Silmaril.Isotope.LambdaSSA.Region.SyntacticCategory
