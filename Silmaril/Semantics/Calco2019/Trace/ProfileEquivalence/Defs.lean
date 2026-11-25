module

public import Silmaril.Semantics.Calco2019.Trace.ProfileStaging.Thms

/-! # The four-interface guarded trace axiom system -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- All the equations of Figure 4. In Vanishing II the outer trace is
applied to the value of the inner trace and uses its output guard. -/
structure Lawful (T : G.FourInterfaceTrace) : Prop extends T.LocalLaws where
  vanishPair {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)
    (hf : G.TraceGuard s.flatTraceBody) :
    T.run hf = T.run (T.guarded (s.innerTraceBody_guard hf))

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
