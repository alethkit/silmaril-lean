module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Network.Thms

/-! # External rows and columns of a weighted network -/

@[expose] public section

universe u v w u' v'

namespace Silmaril.Calco2019.CounterSemiring

variable {A : Type u} {B : Type v} {U : Type w} {A' : Type u'} {B' : Type v'}

/-- Mix external input rows by matrix multiplication, with state rows fixed. -/
def preBoundary [Fintype A] (a : A' → A → Scalar) (f : Network A B U) : Network A' B U
  | .inl x, y => ∑ i, a x i * f (.inl i) y
  | .inr u, y => f (.inr u) y

/-- Mix external output columns by matrix multiplication, with state columns fixed. -/
def postBoundary [Fintype B] (b : B → B' → Scalar) (f : Network A B U) : Network A B' U
  | x, .inl y => ∑ j, f x (.inl j) * b j y
  | x, .inr u => f x (.inr u)

end Silmaril.Calco2019.CounterSemiring
