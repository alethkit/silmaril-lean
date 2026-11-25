module

public import Silmaril.Semantics.Calco2019.Trace.ProfileLaws.Thms
public import Silmaril.Semantics.Calco2019.Trace.ProfileVanishing.Thms

/-! # The body for the inner trace in Figure 4, Vanishing II -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoStateBody

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

/-- Display just the second feedback wire. The first wire is still marked
on both sides, along with the other marked external ports. -/
def innerTraceBody : P.sum (P.sum (P.sum A U) V) B ⟶ P.sum C (P.sum (P.sum D U) V) :=
  restoreTraceBody
    (P.desc (P.desc (P.desc (P.inl ≫ s.entry) s.first) (P.inr ≫ s.entry)) s.second ≫
      P.map P.assoc (𝟙 V))

end Silmaril.Calco2019.Guardedness.TwoStateBody
