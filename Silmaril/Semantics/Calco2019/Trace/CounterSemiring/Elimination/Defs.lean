module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Thms

/-! # Eliminating one feedback state in a scalar matrix -/

@[expose] public section

namespace Silmaril.Calco2019.CounterSemiring.Scalar

/-- Update an entry by summing the direct edge and the route through one
eliminated state, including any number of its self transitions. -/
def eliminate (direct incoming loop outgoing : Scalar) : Scalar :=
  direct + incoming * star loop * outgoing

end Silmaril.Calco2019.CounterSemiring.Scalar
