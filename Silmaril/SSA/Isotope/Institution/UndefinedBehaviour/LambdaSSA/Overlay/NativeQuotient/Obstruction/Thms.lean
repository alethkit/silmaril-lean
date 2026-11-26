module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Obstruction.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Obstruction.Families

/-! # The raw observational model separates installed continuation rewrites -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open LambdaSSA.Region

universe u v

variable {τ : Type v} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]

/-- The guarded Paper quotient identifies a rebuild with a direct product
return. The scope-indexed observation model can supply a non-pair input. -/
theorem not_paper_family_descent :
    ¬ FamilyDescent.{u,v,0,0}
      (Paper.familySetoid (Φ := Φ) ([] : List τ) [product unit unit] [product unit unit]) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.not_paper_family_descent

/-- Initiality in the native continuation quotient requires an uninhabited
empty type. The observation model has no such restriction on bound values. -/
theorem not_continuation_family_descent :
    ¬ FamilyDescent.{u,v,0,0} (continuationSetoid (Φ := Φ) ([] : List τ) [empty] [unit]) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.not_continuation_family_descent

end Silmaril.Isotope.LambdaSSA.UB.Overlay
