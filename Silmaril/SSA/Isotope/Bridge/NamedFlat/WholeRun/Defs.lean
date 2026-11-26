module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Semantics.Defs

/-! # Numbering named cyclic exit observations -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat

universe u

/-- An exit observation uses the first position of its label in the explicit
external list. The payload is already an Isotope value. -/
def numberExit {K α : Type u} [DecidableEq K] (exits : List K) :
    K × Value α → Part (Nat × Value α) :=
  number fun label => exits.findFinIdx? (fun exit => label == exit)

end Silmaril.Isotope.Bridge.NamedFlat
