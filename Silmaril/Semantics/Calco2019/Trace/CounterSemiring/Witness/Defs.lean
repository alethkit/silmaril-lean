module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Network.Thms

/-! # The one-state and two-state weighted systems -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.CounterSemiring

/-- Keep the input-to-output block after eliminating every feedback state. -/
def networkFeedback {A : Type u} {B : Type v} {U : Type w} [Fintype U]
    (f : Network A B U) (a : A) (b : B) : Scalar :=
  eliminateStates Finset.univ f (.inl a) (.inl b)

/-- Use the same row for the entry and for the state. -/
def networkDagger {B : Type v} {U : Type w} [Fintype U]
    (f : U → (B ⊕ U) → Scalar) : U → B → Scalar :=
  networkFeedback fun x => f (x.elim id id)

/-- One immediate exit and one transition of generator weight. -/
def singleLoop (_ : Unit) : (Unit ⊕ Unit) → Scalar
  | .inl _ => 1
  | .inr _ => .generator

/-- Give each of two alternating states the same exit and transition weight. -/
def alternatingLoop (u : Bool) : (Unit ⊕ Bool) → Scalar
  | .inl _ => 1
  | .inr v => if v = !u then .generator else 0

end Silmaril.Calco2019.CounterSemiring
