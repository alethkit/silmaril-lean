module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Witness.Defs
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Data.Fintype.Sum

/-! # Feedback through a partitioned state space -/

@[expose] public section

universe a b u v

namespace Silmaril.Calco2019.CounterSemiring

variable {A : Type a} {B : Type b} {U : Type u} {V : Type v}

/-- Keep the states indexed by an embedding after eliminating the selected states. -/
def retained (e : U ↪ V) (inner : Finset V) (f : Network A B V) : Network A B U :=
  fun x y => eliminateStates inner f (x.map id e) (y.map id e)

/-- Regard the first state block as an external boundary of the inner trace. -/
def innerBody (f : Network A B (U ⊕ V)) : Network (A ⊕ U) (B ⊕ U) V :=
  fun x y => f (Equiv.sumAssoc A U V x) (Equiv.sumAssoc B U V y)

/-- A two-stage sliding diagram. The outgoing leg of the first box enters
the second state block, and the adapter feeds back into the first block. -/
def slidingNetwork (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    Network A B (U ⊕ V)
  | .inl a, .inl b => f (.inl a) (.inl b)
  | .inl a, .inr (.inr v) => f (.inl a) (.inr v)
  | .inr (.inl u), .inl b => f (.inr u) (.inl b)
  | .inr (.inl u), .inr (.inr v) => f (.inr u) (.inr v)
  | .inr (.inr v), .inr (.inl u) => q v u
  | _, _ => 0

/-- Close the adapter's block while keeping the first block. -/
def slidingAfter [Fintype V] (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    Network A B U
  | x, .inl b => f x (.inl b)
  | x, .inr u => ∑ v, f x (.inr v) * q v u

/-- Close the first block while keeping the adapter's block. -/
def slidingBefore [Fintype U] (f : (A ⊕ U) → (B ⊕ V) → Scalar) (q : V → U → Scalar) :
    Network A B V
  | .inl a, y => f (.inl a) y
  | .inr v, y => ∑ u, q v u * f (.inr u) y

end Silmaril.Calco2019.CounterSemiring
