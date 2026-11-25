module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Centrality.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EmptyCentrality

/-! # Exact empty inputs give central pure returns -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => TypeCategory Φ ([] : VCtx τ)

/-- Both interchange paths expose an empty-typed variable after unpacking. -/
theorem whiskerCentral_of_empty_input {B : Comp} (f : ofType (Silmaril.empty : τ) ⟶ B) :
    WhiskerCentral f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EmptyCentrality.whiskerCentral_of_empty_input f

variable {ε : Type w} [HasEff Φ ε]

/-- The typed pure abort expression represents any arrow from the exact empty type. -/
theorem pureReturn_of_empty_input (pe : ε) {B : Comp} (f : ofType (Silmaril.empty : τ) ⟶ B) :
    PureReturn pe f :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EmptyCentrality.pureReturn_of_empty_input pe f

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
