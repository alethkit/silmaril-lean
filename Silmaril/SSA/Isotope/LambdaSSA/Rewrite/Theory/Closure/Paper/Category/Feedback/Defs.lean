module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Postcompose.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Feedback.Congruence

/-! # Feedback on guarded paper continuation classes -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {X Y Z : ContinuationContext Φ Γ}

/-- Pass from native guarded continuation classes through CFG η to the paper category. -/
@[expose] def fromNative : ContinuationContext Φ Γ ⥤ Interface Φ Γ :=
  CfgEta.fromNative ⋙ fromCfgEta

/-- Turn the first exit interface of a guarded producer into local feedback labels. -/
@[expose] def feedback :
    (fromNative.obj X ⟶ fromNative.obj (X.append Y)) → (fromNative.obj X ⟶ fromNative.obj Y) :=
  Quotient.map (ContinuationFamily.feedback (X := X) (Y := Y))
    (fun _ _ h => by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.feedback_congr h)

/-- Act on the outward exits after a fixed prefix of local exits. -/
@[expose] def prepend (X : ContinuationContext Φ Γ) :
    (fromNative.obj Y ⟶ fromNative.obj Z) → (fromNative.obj (X.append Y) ⟶ fromNative.obj (X.append Z)) :=
  Quotient.map (CfgEta.prependFamily X)
    (fun _ _ h => by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.prepend_congr X h)

/-- Present a single-source guarded arrow by its region. -/
@[expose] def singletonArrow {A : τ} {p : Region Φ} (hp : ValueBranches (A :: Γ) p Y.labels) :
    fromNative.obj (ContinuationContext.single A) ⟶ fromNative.obj Y :=
  toHom ⟨fun _ => p, fun _ _ hi =>
    (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hp⟩

/-- Identify the two occurrences of a singleton feedback label, preserving the outward list. -/
@[expose] def collapseLabels (A : τ) (Y : ContinuationContext Φ Γ) :
    fromNative.obj ((ContinuationContext.single A).append ((ContinuationContext.single A).append Y)) ⟶
      fromNative.obj ((ContinuationContext.single A).append Y) :=
  toHom ⟨labelId ∘ Nat.pred, fun _ _ hi => .br (CfgEta.Codiagonal.mergeLabels A Y.labels hi) (.var rfl)⟩

/-- A constructor value returning the new feedback state. -/
@[expose] def stateChange {A D : τ} {a : Tm Φ} (ha : Tm.BranchValue (A :: Γ) a D) :
    ((fromNative (Φ := Φ) (Γ := Γ)).obj (ContinuationContext.single A)) ⟶ fromNative.obj (ContinuationContext.single D) :=
  singletonArrow (.br (ℓ := 0) rfl ha)

/-- Apply the state change only to the first label and forward the outward labels. -/
@[expose] def localStateChange {A D : τ} {a : Tm Φ}
    (Y : ContinuationContext Φ Γ) (ha : Tm.BranchValue (A :: Γ) a D) :
    fromNative.obj ((ContinuationContext.single A).append Y) ⟶
      fromNative.obj ((ContinuationContext.single D).append Y) :=
  toHom ⟨CfgEta.Uniformity.localMap a, by
    intro i T hi
    change At (A :: Y.labels) i T at hi
    cases i with
    | zero => cases Option.some.inj hi; exact .br (ℓ := 0) rfl ha
    | succ i => exact .br (ℓ := i + 1) (show At (D :: Y.labels) (i + 1) T from hi) (.var (i := 0) rfl)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper
