module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Thms
public import Silmaril.Semantics.Calco2019.Trace.Vanishing.Thms

/-! # Vanishing II with the marked external output retained -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.TwoStateBody

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U V : K} (s : TwoStateBody G (P.sum A B) (P.sum C D) U V)

/-- Join the two feedback ports and then restore the separate marked interfaces. -/
def flatTraceBody : P.sum (P.sum A (P.sum U V)) B ⟶ P.sum C (P.sum D (P.sum U V)) :=
  restoreTraceBody (P.desc (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc))

/-- Feed back the second state and display the remaining marked interfaces. -/
def stagedTraceBody (F : G.Fixpoints) : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U) :=
  let close := P.desc (𝟙 _) (F.iterate s.second s.second_guard)
  restoreTraceBody (P.desc (s.entry ≫ close) (s.first ≫ close))

end Silmaril.Calco2019.Guardedness.TwoStateBody
