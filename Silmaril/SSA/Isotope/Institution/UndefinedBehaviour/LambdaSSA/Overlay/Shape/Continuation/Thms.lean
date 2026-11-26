module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Descent

/-! # Descent through the installed native continuation quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open LambdaSSA.Region (SubstitutionEquiv ContinuationFamily ContinuationHom continuationSetoid)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K : List (Ty κ)}

/-- All native substitution equations preserve the lifted observations at
shaped inputs, including fault and both sources of may-divergence. -/
theorem substitutionEquiv_denote {r t : LambdaSSA.Region Φ} (h : SubstitutionEquiv Γ r t L)
    (M : Shape.Model.{u,v,w,x} Φ Γ) (s : M.raw.σ) :
    Shape.denote (.native ⟨r, h.typed.1⟩) M s = Shape.denote (.native ⟨t, h.typed.2⟩) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.substitutionEquiv_denote h M s

/-- The representative map respects pointwise native continuation equivalence. -/
theorem familyDenotation_eq {f g : ContinuationFamily (Φ := Φ) Γ L K}
    (h : (continuationSetoid (Φ := Φ) Γ L K).r f g) :
    familyDenotation.{u,v,w,x} f = familyDenotation.{u,v,w,x} g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation.familyDenotation_eq h

/-- Native continuation families have a well-defined shaped denotation on
the existing quotient at each exact captured, input-label, and output interface. -/
noncomputable def denote : ContinuationHom (Φ := Φ) Γ L K → Denotation.{u,v,w,x} Φ Γ L K :=
  Quotient.lift familyDenotation (fun _ _ h => familyDenotation_eq h)

@[simp] theorem denote_mk (f : ContinuationFamily (Φ := Φ) Γ L K) :
    denote.{u,v,w,x} (Quotient.mk (continuationSetoid Γ L K) f) = familyDenotation f := rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
