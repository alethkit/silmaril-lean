module

public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Defs

/-! # Checked explicit runtime wires for nested γ and θ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime

open OrderedRuntime
open Structured (Ty Data Threaded runtime runtimePort withRuntime nextRuntime Instruction Opcode)

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {args ins out outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

abbrev thetaNode {Op : Dialect (V := V) (S := PUnit.{u + 1})}
    (live : Origin args past runtime) (wires : Wires args past ins)
    (bodySigs : List (Ports (Ty V))) : Node Op args past (Threaded ins) :=
  ⟨Threaded ins, .theta (Threaded ins), withRuntime live wires, fun _ => bodySigs⟩

/-- Every binding consumes its designated live token. Each child enters at
its own boundary token, and the successor is the newest output's token. -/
inductive Checked (P E : Dialect.{u, v} V PUnit.{u + 1}) :
    {args outs : Ports (Ty V)} → Data args → Data outs →
    {past sigs : List (Ports (Ty V))} → Origin (Threaded args) past runtime →
    Term (Opcode P E) (Threaded args) past sigs (Threaded outs) → Type (max u v)
  | ret {args outs : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past outs) :
      Checked P E a b live (.ret (withRuntime live wires))
  | primitive {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (i : Data ins) (o : Data out)
      (op : Instruction P E ins out) (wires : Wires (Threaded args) past ins)
      {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      Checked P E a b (nextRuntime past out) rest →
      Checked P E a b live (.bind (.ofBase (Structured.primitiveNode live i o op wires))
        (fun j => j.elim0) rest)
  | gamma {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (extra : Nat) (choice : Origin (Threaded args) past (.control (extra + 2)))
      (live : Origin (Threaded args) past runtime) (i : Data ins) (o : Data out)
      (wires : Wires (Threaded args) past ins) (childSigs : Fin (extra + 2) → List (Ports (Ty V)))
      {children : ∀ j, Term (Opcode P E) (Threaded ins) [] (childSigs j) (Threaded out)}
      {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      (∀ j, Checked P E i o (.arg (runtimePort ins)) (children j)) →
      Checked P E a b (nextRuntime past out) rest →
      Checked P E a b live (.bind (.ofBase (Structured.gammaNode (out := out) extra choice live wires childSigs)) children rest)
  | theta {args outs ins : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (i : Data ins)
      (wires : Wires (Threaded args) past ins) (bodySigs : List (Ports (Ty V)))
      {children : Fin 1 → Term (Opcode P E) (Threaded ins) [] bodySigs (Threaded (Theta.BodyResults ins))}
      {rest : Term (Opcode P E) (Threaded args) (past ++ [Threaded ins]) sigs (Threaded outs)} :
      (∀ j, Checked P E i (.control i) (.arg (runtimePort ins)) (children j)) →
      Checked P E a b (nextRuntime past ins) rest →
      Checked P E a b live (.bind (thetaNode live wires bodySigs) children rest)

abbrev EntryChecked {a : Data args} {b : Data outs}
    (t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)) :=
  Checked P E a b (.arg (runtimePort args)) t

/-- Generator signatures retain their last port as a unit slot after erasure. -/
inductive ThreadedOp (D : Dialect.{u, v} V PUnit.{u + 1}) : Dialect.{u, max u v} V PUnit.{u + 1} where
  | op {ins outs : Ports (Ty V)} : D ins outs → ThreadedOp D (Threaded ins) (Threaded outs)

abbrev ErasedOp (P E : Dialect.{u, v} V PUnit.{u + 1}) := Instruction (ThreadedOp P) (ThreadedOp E)

def eraseInstruction (op : Instruction P E ins outs) : ErasedOp P E (Threaded ins) (Threaded outs) :=
  match op with
  | .pure p => .pure (.op p)
  | .effect e => .effect (.op e)

/-- Keep typed numbering and all port positions. The old token fields become
unit in the implicit model. Only primitive opcodes require a translation. -/
def Checked.erase :
    {args outs : Ports (Ty V)} → {a : Data args} → {b : Data outs} →
    {past sigs : List (Ports (Ty V))} → {live : Origin (Threaded args) past runtime} →
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)} →
    Checked P E a b live t → Term (ErasedOp P E) (Threaded args) past sigs (Threaded outs)
  | _, _, _, _, _, _, _, _, .ret live wires => .ret (withRuntime live wires)
  | _, _, _, _, _, _, _, _, .primitive live _ _ op wires rest =>
    .bind ⟨_, .base (.simple (eraseInstruction op)), withRuntime live wires, fun j => j.elim0⟩
      (fun j => j.elim0) rest.erase
  | _, _, _, _, _, _, _, _, .gamma extra choice live _ _ wires childSigs arms rest =>
    .bind ⟨_, .base (.gamma extra), .cons choice (withRuntime live wires), childSigs⟩
      (fun j => (arms j).erase) rest.erase
  | _, _, _, _, _, _, _, _, .theta live _ wires bodySigs children rest =>
    .bind (thetaNode live wires bodySigs) (fun j => (children j).erase) rest.erase

variable {σ : Type (max u w)} (m : Structured.Model P E (StateM σ))

/-- The unit slots leave state handling to the existing ordered model. -/
def erasedModel : Structured.Model (ThreadedOp P) (ThreadedOp E) (StateM σ) where
  value := m.value
  runPure
    | @ThreadedOp.op _ _ ins _ op, input =>
      withRuntime PUnit.unit (m.runPure op (Structured.splitRuntime ins input).1)
  effect
    | @ThreadedOp.op _ _ ins _ op, input =>
      withRuntime PUnit.unit <$> m.effect op (Structured.splitRuntime ins input).1

/-- Erase token slots in returned data and observe the final token separately. -/
def boundaryResult {value : V → Type (max u w)}
    (result : Tuple (Structured.RuntimeValues value σ) (Threaded outs)) :
    OrderedState.Configuration value σ (Threaded outs) :=
  (Structured.eraseTuple result, result.get (runtimePort outs))

/-- Observe the erased graph with the same implicit semantics as any ordered
nested term. Both the unit-ending output tuple and the final state are returned. -/
noncomputable def observe {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked (a := a) (b := b) g.toTerm)
    (input : Tuple (Structured.RuntimeValues m.value σ) (Threaded args)) :
    _root_.Part (OrderedState.Configuration m.value σ (Threaded outs)) :=
  OrderedState.observe (erasedModel m) checked.erase.toGraph (Structured.eraseTuple input)
    (input.get (runtimePort args))

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime
