module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Defs

/-! # The representative contract for continuation quotient descent -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open LambdaSSA.Region (ContinuationFamily)

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L K : List τ}

/-- Interpret a family member at its exact value binder and exit interface. -/
noncomputable def familyDenotation (family : ContinuationFamily (Φ := Φ) Γ L K) (i : Fin L.length) :
    Denotation.{u,v,w,x} Φ (L.get i :: Γ) K :=
  nativeDenotation ⟨family.val i, (family.property (A := L.get i) (by simp [At])).hasType⟩

/-- Descent requires the same semantic map on every representative. -/
def FamilyDescent (S : Setoid (ContinuationFamily (Φ := Φ) Γ L K)) : Prop :=
  ∃ lift : Quotient S → (i : Fin L.length) → Denotation.{u,v,w,x} Φ (L.get i :: Γ) K,
    ∀ family i, lift (Quotient.mk S family) i = familyDenotation family i

end Silmaril.Isotope.LambdaSSA.UB.Overlay
