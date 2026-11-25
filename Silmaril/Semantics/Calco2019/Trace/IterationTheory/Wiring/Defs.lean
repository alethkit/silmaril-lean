module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Terms.Defs

/-! # Finite equation graphs for iteration terms -/

@[expose] public section

universe w

namespace Silmaril.Calco2019.IterationTheory

/-- A graph instruction is a ranked head or an unlabelled jump to another state. -/
inductive Instruction (σ : Signature.{w}) (E S : Type)
  | jump (next : S)
  | head (row : Head σ E S)

namespace Instruction

variable {σ : Signature.{w}} {E R S T : Type}

/-- Rename states and connect each exit to a new instruction. -/
def connect (f : S → T) (exit : E → Instruction σ R T) :
    Instruction σ E S → Instruction σ R T
  | .jump s => .jump (f s)
  | .head .bottom => .head .bottom
  | .head (.exit e) => exit e
  | .head (.node a child) => .head (.node a (f ∘ child))

end Instruction

/-- A finite presentation with one entry per input port. -/
structure Wiring (σ : Signature.{w}) (I E : Arity) where
  states : Arity
  entry : I → states
  row : states → Instruction σ E states

namespace Wiring

variable {σ : Signature.{w}} {I J E : Arity}

/-- A base map immediately returns the selected parameter. -/
def base (f : I → E) : Wiring σ I E :=
  ⟨I, id, fun i => .head (.exit (f i))⟩

/-- The input state emits the generator's label. Its children return at the
corresponding argument ports in order. -/
def generator (a : σ.Symbol) : Wiring σ Arity.one (Arity.ofNat (σ.arity a)) where
  states := Arity.one.sum (Arity.ofNat (σ.arity a))
  entry := Sum.inl
  row
    | .inl _ => .head (.node a Sum.inr)
    | .inr i => .head (.exit i)

/-- Pairing forms the disjoint union of the state sets. -/
def pair (f : Wiring σ I E) (g : Wiring σ J E) : Wiring σ (I.sum J) E where
  states := f.states.sum g.states
  entry := Sum.map f.entry g.entry
  row
    | .inl s => (f.row s).connect Sum.inl (fun e => .head (.exit e))
    | .inr s => (g.row s).connect Sum.inr (fun e => .head (.exit e))

/-- Composition connects the first graph's exits to the second graph's entries. -/
def comp (f : Wiring σ I J) (g : Wiring σ J E) : Wiring σ I E where
  states := f.states.sum g.states
  entry i := .inl (f.entry i)
  row
    | .inl s => (f.row s).connect Sum.inl (fun j => .jump (.inr (g.entry j)))
    | .inr s => (g.row s).connect Sum.inr (fun e => .head (.exit e))

/-- Iteration connects each feedback exit back to its matching entry. -/
def iterate (f : Wiring σ I (E.sum I)) : Wiring σ I E where
  states := f.states
  entry := f.entry
  row s := (f.row s).connect id
    (Sum.elim (fun e => .head (.exit e)) (fun i => .jump (f.entry i)))

end Wiring

namespace Term

variable {σ : Signature.{w}}

/-- Compile a term into the finite graph of its operations, exits and jumps. -/
def wiring : {I E : Arity} → Term σ I E → Wiring σ I E
  | _, _, .base f => .base f
  | _, _, .generator a => .generator a
  | _, _, .pair f g => .pair (wiring f) (wiring g)
  | _, _, .comp f g => .comp (wiring f) (wiring g)
  | _, _, .iterate f => .iterate (wiring f)

end Term

end Silmaril.Calco2019.IterationTheory
