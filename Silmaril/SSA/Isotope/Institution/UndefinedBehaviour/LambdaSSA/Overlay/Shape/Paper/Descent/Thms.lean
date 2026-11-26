module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Soundness

/-! # Shaped observational descent for the guarded Paper quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open LambdaSSA.Region (ContinuationFamily)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K : List (Ty κ)}

/-- All installed guarded Paper equations preserve the lifted behaviour
of exactly typed native regions in shaped models. -/
theorem eqv_denote {r t : LambdaSSA.Region Φ} (h : LambdaSSA.Region.Paper.Eqv Γ r t L)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native ⟨r, h.typed.1⟩) M s = Shape.denote (.native ⟨t, h.typed.2⟩) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent.eqv_denote h M s

/-- Pointwise Paper equivalence preserves the denotation of each member at
its exact captured context and input-label type. -/
theorem familyDenotation_eq {f g : ContinuationFamily (Φ := Φ) Γ L K}
    (h : (LambdaSSA.Region.Paper.familySetoid (Φ := Φ) Γ L K).r f g) :
    Continuation.familyDenotation.{u,v,w,x} f = Continuation.familyDenotation.{u,v,w,x} g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Descent.familyDenotation_eq h

/-- Interpret the existing guarded Paper continuation quotient in the
shaped UB overlay. -/
noncomputable def denote :
    LambdaSSA.Region.Paper.Hom (Φ := Φ) Γ L K → Continuation.Denotation.{u,v,w,x} Φ Γ L K :=
  Quotient.lift Continuation.familyDenotation (fun _ _ h => familyDenotation_eq h)

@[simp] theorem denote_mk (f : ContinuationFamily (Φ := Φ) Γ L K) :
    denote.{u,v,w,x} (Quotient.mk (LambdaSSA.Region.Paper.familySetoid Γ L K) f) =
      Continuation.familyDenotation f := rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
