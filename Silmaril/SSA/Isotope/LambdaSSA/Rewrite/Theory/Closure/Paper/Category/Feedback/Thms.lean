module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Feedback.Quotient

/-! # Feedback and outward sequencing in the guarded paper category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

/-- The projection to paper classes keeps the feedback representative. -/
@[simp] theorem feedback_fromCfgEta
    (f : CfgEta.fromNative.obj X ⟶ CfgEta.fromNative.obj (X.append Y)) :
    feedback (X := X) (Y := Y) (fromCfgEta.map f) = fromCfgEta.map (CfgEta.feedback f) :=
  Quotient.inductionOn f (fun _ => rfl)

/-- The projection to paper classes keeps the same prefixed continuations. -/
@[simp] theorem prepend_fromCfgEta (X : ContinuationContext Φ Γ)
    (g : CfgEta.fromNative.obj Y ⟶ CfgEta.fromNative.obj Z) :
    prepend X (fromCfgEta.map g) = fromCfgEta.map (CfgEta.prepend X g) :=
  Quotient.inductionOn g (fun _ => rfl)

/-- Outward sequencing commutes with guarded feedback. -/
theorem feedback_postcompose
    (f : fromNative.obj X ⟶ fromNative.obj (X.append Y))
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    feedback (X := X) (Y := Y) f ≫ g =
      feedback (X := X) (Y := Z) (f ≫ prepend X g) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_postcompose f g

@[reassoc] theorem appendInl_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInl Y) ≫ prepend X g = fromNative.map (X.appendInl Z) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.appendInl_prepend X g

@[reassoc] theorem appendInr_prepend (X : ContinuationContext Φ Γ)
    (g : fromNative.obj Y ⟶ fromNative.obj Z) :
    fromNative.map (X.appendInr Y) ≫ prepend X g = g ≫ fromNative.map (X.appendInr Z) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.appendInr_prepend X g

open ContinuationContext (single)

/-- Two singleton feedback cuts over the same state agree with one cut
after forwarding the duplicate feedback label. -/
theorem feedback_codiagonal (A : τ) (Y : ContinuationContext Φ Γ)
    (f : fromNative.obj (single A) ⟶ fromNative.obj ((single A).append ((single A).append Y))) :
    feedback (X := single A) (Y := Y)
      (feedback (X := single A) (Y := (single A).append Y) f) =
    feedback (X := single A) (Y := Y) (f ≫ collapseLabels A Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_codiagonal A Y f

/-- A constructor-valued local simulation square in the quotient commutes with feedback. -/
theorem feedback_uniformity {A D : τ} {a : Tm Φ} (Y : ContinuationContext Φ Γ)
    (ha : Tm.BranchValue (A :: Γ) a D)
    (f : fromNative.obj (single A) ⟶ fromNative.obj ((single A).append Y))
    (g : fromNative.obj (single D) ⟶ fromNative.obj ((single D).append Y))
    (square : f ≫ localStateChange Y ha = stateChange ha ≫ g) :
    feedback (X := single A) (Y := Y) f =
      stateChange ha ≫ feedback (X := single D) (Y := Y) g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_uniformity Y ha f g square

@[reassoc] theorem collapseLabels_left (A : τ) (Y : ContinuationContext Φ Γ) :
    fromNative.map ((single A).appendInl ((single A).append Y)) ≫ collapseLabels A Y =
      fromNative.map ((single A).appendInl Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.collapseLabels_left A Y

@[reassoc] theorem collapseLabels_right (A : τ) (Y : ContinuationContext Φ Γ) :
    fromNative.map ((single A).appendInr ((single A).append Y)) ≫ collapseLabels A Y =
      𝟙 (fromNative.obj ((single A).append Y)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.collapseLabels_right A Y

@[reassoc] theorem localStateChange_left (Y : ContinuationContext Φ Γ)
    {A D : τ} {a : Tm Φ} (ha : Tm.BranchValue (A :: Γ) a D) :
    fromNative.map ((single A).appendInl Y) ≫ localStateChange Y ha =
      stateChange ha ≫ fromNative.map ((single D).appendInl Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.localStateChange_left Y ha

@[reassoc] theorem localStateChange_right (Y : ContinuationContext Φ Γ)
    {A D : τ} {a : Tm Φ} (ha : Tm.BranchValue (A :: Γ) a D) :
    fromNative.map ((single A).appendInr Y) ≫ localStateChange Y ha =
      fromNative.map ((single D).appendInr Y) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.localStateChange_right Y ha

end Silmaril.Isotope.LambdaSSA.Region.Paper
