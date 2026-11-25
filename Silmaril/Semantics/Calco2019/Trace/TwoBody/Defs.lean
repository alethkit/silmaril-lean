module

public import Silmaril.Semantics.Calco2019.Trace.Equivalence.Thms

/-! # Sliding with two bodies and separate external interfaces -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- The two bodies around a feedback loop have separate entries and returns. -/
structure TwoBody (P : Coproducts K) (A E B D U V : K) where
  first : P.sum A U ⟶ P.sum B V
  second : P.sum E V ⟶ P.sum D U

namespace TwoBody

variable {A E B D U V : K} (c : TwoBody P A E B D U V)

def firstEntry : A ⟶ P.sum (P.sum B D) V :=
  P.inl ≫ c.first ≫ P.map P.inl (𝟙 V)

def firstStep : U ⟶ P.sum (P.sum B D) V :=
  P.inr ≫ c.first ≫ P.map P.inl (𝟙 V)

def secondEntry : E ⟶ P.sum (P.sum B D) U :=
  P.inl ≫ c.second ≫ P.map P.inr (𝟙 U)

def secondStep : V ⟶ P.sum (P.sum B D) U :=
  P.inr ≫ c.second ≫ P.map P.inr (𝟙 U)

/-- Cut the loop before the first body, with its state as the recursive summand. -/
def cutFirst : P.sum (P.sum A E) U ⟶ P.sum (P.sum B D) U :=
  P.desc (P.desc (c.firstEntry ≫ P.desc P.inl c.secondStep) c.secondEntry)
    (c.firstStep ≫ P.desc P.inl c.secondStep)

/-- Cut the loop before the second body, with its state as the recursive summand. -/
def cutSecond : P.sum (P.sum A E) V ⟶ P.sum (P.sum B D) V :=
  P.desc (P.desc c.firstEntry (c.secondEntry ≫ P.desc P.inl c.firstStep))
    (c.secondStep ≫ P.desc P.inl c.firstStep)

end TwoBody

end Silmaril.Calco2019.Guardedness
