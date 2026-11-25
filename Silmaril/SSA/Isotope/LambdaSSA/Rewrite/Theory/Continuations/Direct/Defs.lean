module

public import Silmaril.SSA.Isotope.LambdaSSA.LabelSubstitution.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Defs

/-! # Regions without locally defined blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region

/-- Branches, lets, case splits and empty CFGs require no local iteration. -/
def NoLocalBlocks {Φ : Type*} : Region Φ → Prop
  | .br _ _ => True
  | .let₁ _ body | .let₂ _ body => NoLocalBlocks body
  | .case _ left right => NoLocalBlocks left ∧ NoLocalBlocks right
  | .cfg entry n _ => n = 0 ∧ NoLocalBlocks entry

end Silmaril.Isotope.LambdaSSA.Region
