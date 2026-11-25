module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Elimination.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.CounterSemiringElimination

/-! # Two scalar feedback eliminations commute -/

public section

namespace Silmaril.Calco2019.CounterSemiring.Scalar

/-- Eliminating two states in either order updates each remaining entry
identically. The two loops are `a` and `d`, and the two edges between them
are `b` and `c`. -/
theorem eliminate_pair (direct intoFirst intoSecond fromFirst fromSecond a b c d : Scalar) :
    eliminate (eliminate direct intoFirst a fromFirst)
        (eliminate intoSecond intoFirst a b) (eliminate d c a b)
        (eliminate fromSecond c a fromFirst) =
      eliminate (eliminate direct intoSecond d fromSecond)
        (eliminate intoFirst intoSecond d c) (eliminate a b d c)
        (eliminate fromFirst b d fromSecond) :=
  Proofs.CounterSemiring.eliminate_pair direct intoFirst intoSecond fromFirst fromSecond a b c d

end Silmaril.Calco2019.CounterSemiring.Scalar
