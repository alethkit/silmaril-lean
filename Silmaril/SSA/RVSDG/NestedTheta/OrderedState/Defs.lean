module

public import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Lift.Defs

/-! # Nested γ and θ with one ordered state

Ports contain only values, selectors, and unit state slots. The live state is
private to the computation and is passed separately in the finite relation.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.OrderedState

open CategoryTheory
open OrderedRuntime
open Structured (Instruction Values Ty)

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args ins outs carried : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

abbrev Configuration (value : V → Type (max u w)) (σ : Type (max u w)) (ts : Ports (Ty V)) :=
  Tuple (Values value) ts × σ

/-- A tagged body completion retains its final state on either branch. -/
def tagged {value : V → Type (max u w)} (again : Bool)
    (output : Configuration value σ carried) :
    Configuration value σ (Theta.BodyResults carried) :=
  (.cons ⟨if again then 1 else 0⟩ output.1, output.2)

variable (m : Structured.Model P E (StateM σ))

/-- The independent local rule uses a total state primitive, the selected arm,
or finite iteration on configurations of carried data and current state. -/
def kindExec :
    {ins outs : Ports (Ty V)} → (kind : Kind (Instruction P E) ins outs) →
    (Fin kind.arity → Configuration m.value σ kind.entry → Configuration m.value σ kind.exit → Prop) →
    Configuration m.value σ ins → Configuration m.value σ outs → Prop
  | _, _, .base (.simple opcode), _, (input, state), output =>
    (m.step opcode input).run state = output
  | _, _, .base (.gamma _), child, (.cons tag payload, state), output =>
    child tag.down (payload, state) output
  | _, _, .theta _, child, input, output =>
    Theta.Iterate (fun x again y => child (0 : Fin 1) x (tagged again y)) input output

/-- A finite derivation follows the typed wire dependencies in binding order.
Each child opens a fresh value scope, taking the current state at entry. -/
def exec :
    {args outs : Ports (Ty V)} → {past sigs : List (Ports (Ty V))} →
    Term (Instruction P E) args past sigs outs → Tuple (Values m.value) args →
    Locals (Values m.value) past → σ → Configuration m.value σ outs → Prop
  | _, _, _, _, .ret wires, input, locals, state, output =>
    (wires.read input locals, state) = output
  | _, _, _, _, .bind node children rest, input, locals, state, output =>
    ∃ result, kindExec m node.kind (fun i x y => exec (children i) x.1 PUnit.unit x.2 y)
      (node.inputs.read input locals, state) result ∧
        exec rest input (locals.snoc result.1) result.2 output

/-- Use the same primitive state actions as the ordered runtime model, lifting
each total result together with its final state as in the whole-region model. -/
def interpretation : MonadicModel.{u, _, max u w} (Instruction P E) (StateT σ _root_.Part) where
  value := m.value
  snapshot _ := PUnit
  primitive := m.liftTotal.step

/-- The ordered interpretation as a Kleisli morphism with a pure tuple boundary. -/
noncomputable def denote (t : Term (Instruction P E) args [] sigs outs) :
    Kleisli.mk (ofTypeMonad.{max u w} (StateT σ _root_.Part)) (Tuple (Values m.value) args) ⟶
      Kleisli.mk (ofTypeMonad.{max u w} (StateT σ _root_.Part)) (Tuple (Values m.value) outs) :=
  t.denoteWith (M := StateT σ _root_.Part) (interpretation m)

/-- Observe the numbered graph via its exact typed decoder. -/
noncomputable def observe (g : Graph (Instruction P E) args [] sigs outs)
    (input : Tuple (Values m.value) args) (state : σ) : _root_.Part (Configuration m.value σ outs) :=
  (denote m g.toTerm).of input state

end Silmaril.SSA.RVSDG.NestedTheta.OrderedState
