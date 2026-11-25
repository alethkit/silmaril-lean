module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Observations.Thms

/-! # Separate argument slots in a ranked system

Extra copies allow the commutative schema to route repeated arguments
independently. The original equations and their states embed into the
expanded system.
-/

@[expose] public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

variable {σ : Signature.{u}} {E : Type v} {S : Type w} {T : Type z}

namespace Head

/-- The argument count of this equation, with no slots at bottom or an exit. -/
def slots : Head σ E S → Nat
  | .node sym _ => σ.arity sym
  | _ => 0

/-- The recursive state selected by a slot. -/
def argument : (e : Head σ E S) → Fin e.slots → S
  | .node _ child => child
  | .bottom | .exit _ => Fin.elim0

/-- Reuse the head with a new family of recursive arguments. -/
def withArguments : (e : Head σ E S) → (Fin e.slots → T) → Head σ E T
  | .node sym _, child => .node sym child
  | .bottom, _ => .bottom
  | .exit p, _ => .exit p

/-- At a node, distinct slots have distinct recursive states. -/
def HasDistinctArguments : Head σ E S → Prop
  | .node _ child => Function.Injective child
  | _ => True

end Head

variable (g : System σ E S) (pick : T → S)

/-- Keep the source states and add one fresh state per representative argument slot. -/
abbrev ExpandedState := S ⊕ (Σ t : T, Fin (g (pick t)).slots)

/-- Each fresh state is a copy of the original state at that argument. -/
def originalState : ExpandedState g pick → S
  | .inl s => s
  | .inr ⟨t, i⟩ => (g (pick t)).argument i

/-- Run copies of the original equations on the enlarged state set. -/
def expandedSystem : System σ E (ExpandedState g pick) :=
  fun x => (g (originalState g pick x)).mapState Sum.inl

/-- The equation for each representative, using distinct argument indices. -/
def representativeBody : T → Head σ E (ExpandedState g pick) :=
  fun t => (g (pick t)).withArguments (fun i => .inr ⟨t, i⟩)

/-- Project the enlarged states to the target system. -/
def expandedProjection (p : S → T) : ExpandedState g pick → T := p ∘ originalState g pick

end Silmaril.Calco2019.IterationTheory
