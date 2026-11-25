module

public import Silmaril.Semantics.Calco2019.Trace.Thms

/-! # Sliding through a coproduct with a shared result -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- Close the feedback path after the adapter, passing through immediate returns. -/
def slideAfter {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U) :
    P.sum A U ⟶ P.sum B U :=
  f ≫ P.desc P.inl h

/-- Close the feedback path before the adapter. The entry still begins at the body. -/
def slideBefore {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U) :
    P.sum A V ⟶ P.sum B V :=
  P.desc (P.inl ≫ f) (h ≫ P.desc P.inl (P.inr ≫ f))

end Silmaril.Calco2019.Guardedness
