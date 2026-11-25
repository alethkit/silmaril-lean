module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Thms

/-! # Iteration laws for nondeterministic printing with hangs -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces

noncomputable instance {A : Type u} : Elgot.Iterate (Traces A) where
  iter := iterate

end Silmaril.Calco2019.Examples.Printing.HangTraces
