module

public import Mathlib.Data.Set.Defs

/-!
# Positive ground rules

A presentation is a set of ground instances. A schema with side conditions
contributes exactly the instances for which those conditions hold. Each rule
asks only for positive derivations of its finitely many premises.
-/

@[expose] public section

namespace Silmaril.Semantics.SOS

universe u v

/-- An ordered list of premises and a single conclusion. The empty list gives a fact. -/
structure Rule (J : Type u) where
  premises : List J
  conclusion : J

/-- Rename every occurrence, preserving the order and multiplicity of premises. -/
def Rule.map {J : Type u} {K : Type v} (f : J → K) (r : Rule J) : Rule K :=
  ⟨r.premises.map f, f r.conclusion⟩

/-- A predicate satisfies a clause if truth of every premise implies its conclusion. -/
def Rule.Holds {J : Type u} (M : J → Prop) (r : Rule J) : Prop :=
  (∀ j ∈ r.premises, M j) → M r.conclusion

/-- A predicate is closed under every rule in the presentation. -/
def Closed {J : Type u} (R : Set (Rule J)) (M : J → Prop) : Prop :=
  ∀ r ∈ R, r.Holds M

/-- One application of a rule to premises in the supplied predicate. -/
def immediate {J : Type u} (R : Set (Rule J)) (M : J → Prop) : J → Prop :=
  fun j => ∃ r ∈ R, r.conclusion = j ∧ ∀ p ∈ r.premises, M p

/-- The inductively generated judgment predicate. -/
inductive Derives {J : Type u} (R : Set (Rule J)) : J → Prop where
  | apply {r : Rule J} (member : r ∈ R) (premises : ∀ j ∈ r.premises, Derives R j) :
      Derives R r.conclusion

end Silmaril.Semantics.SOS
