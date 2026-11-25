module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.OrderedState.Adequacy

/-! # Finite full-state observations of nested γ and θ -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState

open CategoryTheory
open OrderedRuntime
open Structured (Instruction Values Ty)

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable (m : Structured.Model P E (StateM σ))

/-- At any prefix, a finite observation includes the entire output tuple and final state. -/
theorem mem_denoteOpen (t : Term (Instruction P E) args past sigs outs)
    (input : Tuple (Values m.value) args) (locals : Locals (Values m.value) past)
    (state : σ) (output : Configuration m.value σ outs) :
    output ∈ (t.denoteOpenWith (interpretation m) input locals).run state ↔
      exec m t input locals state output :=
  Proofs.mem_denoteOpen m t input locals state output

/-- Encoding the term as a graph preserves its stateful computation. -/
theorem observe_toGraph (t : Term (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (state : σ) :
    observe m t.toGraph input state = (denote m t).of input state := by
  rw [observe, Term.toTerm_toGraph]

/-- A numbered graph has a given finite observation exactly when its typed
decoder has a finite derivation of that full result and final state. -/
theorem mem_observe (g : Graph (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (state : σ) (output : Configuration m.value σ outs) :
    output ∈ observe m g input state ↔ exec m g.toTerm input PUnit.unit state output :=
  mem_denoteOpen m g.toTerm input PUnit.unit state output

theorem observe_eq_some (g : Graph (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (state : σ) (output : Configuration m.value σ outs) :
    observe m g input state = _root_.Part.some output ↔ exec m g.toTerm input PUnit.unit state output :=
  _root_.Part.eq_some_iff.trans (mem_observe m g input state output)

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState
