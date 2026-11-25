module

public import Silmaril.Semantics.Calco2019.Trace.Uniformity.Thms

/-! # The two-state coproduct profile of guarded feedback -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- A feedback body with separate entry, first state, and second state branches.
The two state branches are guarded simultaneously in both recursive outputs. -/
structure TwoStateBody (G : Guardedness P) (A B U V : K) where
  entry : A ⟶ P.sum (P.sum B U) V
  first : U ⟶ P.sum (P.sum B U) V
  second : V ⟶ P.sum (P.sum B U) V
  guarded : G.nested (P.desc first second)

end Silmaril.Calco2019.Guardedness
