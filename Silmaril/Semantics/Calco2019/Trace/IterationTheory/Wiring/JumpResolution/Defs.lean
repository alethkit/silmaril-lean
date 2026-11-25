module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

/-! # Removing unlabelled jumps from finite equation graphs -/

@[expose] public section

universe w

namespace Silmaril.Calco2019.IterationTheory

namespace Instruction

variable {σ : Signature.{w}} {E S : Type}

/-- The row has a state transition without a ranked label. -/
def IsJump : Instruction σ E S → Prop
  | .jump _ => True
  | .head _ => False

end Instruction

namespace Wiring

variable {σ : Signature.{w}} {I E : Arity}

/-- A finite graph whose rows are already ranked. -/
structure Ranked (σ : Signature.{w}) (I E : Arity) where
  states : Arity
  entry : I → states
  system : System σ E states

/-- Regard a ranked graph as a graph without unlabelled transitions. -/
def Ranked.toWiring (g : Ranked σ I E) : Wiring σ I E :=
  ⟨g.states, g.entry, fun s => .head (g.system s)⟩

variable (g : Wiring σ I E)

/-- States other than a selected jump state. -/
abbrev without (s : g.states) : Arity :=
  ⟨{r : g.states // r ≠ s}, Finite.of_injective Subtype.val Subtype.val_injective⟩

/-- In the graph without a state, redirect every reference to that state
to the target of its jump. -/
noncomputable def redirect (s : g.states) (t : g.without s) (r : g.states) : g.without s :=
  open Classical in
  if h : r = s then t else ⟨r, h⟩

/-- Delete a jump to a different state and redirect all its incoming edges. -/
noncomputable abbrev contract (s : g.states) (t : g.without s) : Wiring σ I E where
  states := g.without s
  entry := g.redirect s t ∘ g.entry
  row r := (g.row r.val).connect (g.redirect s t) (fun e => .head (.exit e))

/-- Replace a self-jump by an explicit bottom row. -/
noncomputable abbrev cut (s : g.states) : Wiring σ I E where
  states := g.states
  entry := g.entry
  row r := open Classical in if r = s then .head .bottom else g.row r

/-- The number of unlabelled transitions in the graph. -/
noncomputable def jumpCount : Nat := Nat.card {s : g.states // (g.row s).IsJump}

/-- The normalization steps linking a wiring to a ranked graph. A cycle of
jumps contracts to a self-jump, which takes the bottom row. -/
inductive Normalizes : Wiring σ I E → Ranked σ I E → Prop
  | done (r : Ranked σ I E) : Normalizes r.toWiring r
  | cut {g : Wiring σ I E} {r : Ranked σ I E} (s : g.states)
      (row : g.row s = .jump s) (rest : Normalizes (g.cut s) r) : Normalizes g r
  | contract {g : Wiring σ I E} {r : Ranked σ I E} (s : g.states) (t : g.without s)
      (row : g.row s = .jump t.val) (rest : Normalizes (g.contract s t) r) : Normalizes g r

end Wiring

end Silmaril.Calco2019.IterationTheory
