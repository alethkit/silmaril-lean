module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Defs

/-! # The exact guarded distributor on structural values -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton (map_centralCopies CentralCopies)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

local infixr:70 " ×ₜ " => Silmaril.product
local infixr:65 " ⊕ₜ " => Silmaril.coprod

private theorem inverse_mem (X A B : τ) :
    Extension.Singleton.StructuralValues.HomProperty (JoinedStep (Φ := Φ) pe)
      (guardedDistributorIso pe X A B).hom := by
  obtain ⟨f, hf, eq⟩ := inverse_copying_lift (Φ := Φ) pe X A B
  have h : CentralCopies (JoinedStep pe) ((projection pe).map f) := map_centralCopies _ hf
  exact ⟨eq ▸ h, inverse_discard pe X A B⟩

/-- Both directions of the exact guarded distributor belong to the structural value category. -/
noncomputable def distributor (X A B : τ) :
    ofSyntaxType (Φ := Φ) pe ((X ×ₜ A) ⊕ₜ (X ×ₜ B)) ≅ ofSyntaxType pe (X ×ₜ (A ⊕ₜ B)) :=
  WideSubcategory.isoMk (guardedDistributorIso pe X A B).symm
    (Extension.Singleton.StructuralValues.of_discardPreservingReturn _ (forward_mem pe X A B))
    (inverse_mem pe X A B)

/-- Inclusion computes the two literal guarded maps. -/
theorem inclusion_mapIso_distributor (X A B : τ) :
    (inclusion (Φ := Φ) pe).mapIso (distributor pe X A B) =
      (guardedDistributorIso pe X A B).symm :=
  Iso.ext rfl

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
