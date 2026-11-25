module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Matrices.Thms
public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Witness.Defs
public import Silmaril.Semantics.Calco2019.Trace.Total.Thms

/-! # Total trace by eliminating all finite feedback states -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

/-- Eliminate the feedback indices and read off the external matrix. -/
noncomputable def feedback :
    Guardedness.Feedback (Guardedness.greatest (coproducts : Coproducts Object.{u})) :=
  fun f _ => Matrix.of (networkFeedback (fun x y => f x y))

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix
