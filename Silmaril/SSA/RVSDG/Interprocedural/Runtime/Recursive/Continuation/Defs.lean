module

public import Mathlib.Logic.Relation
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Defs

/-! An explicit continuation machine for finite linked calls and selected γ arms. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {outs : Ports (Ty V S)}

/-- A frame preserves the caller's arguments and previously bound tuples.
The next result supplies exactly the new binding expected by the suffix. -/
inductive Stack (m : Machine.{u, v, w} Op) : Ports (Ty V S) → Ports (Ty V S) → Type (max u v w) where
  | halt {outs : Ports (Ty V S)} : Stack m outs outs
  | resume {args head outs final : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}
      (suffix : NestedTheta.Term (Instruction Op) args (past ++ [head]) sigs outs)
      (entry : Tuple m.Val args) (locals : Locals m.Val past) (outer : Stack m outs final) :
      Stack m head final

/-- The active job's output type matches the stack's next input type. -/
inductive State (m : Machine.{u, v, w} Op) (final : Ports (Ty V S)) : Type (max u v w) where
  | eval {outs : Ports (Ty V S)} (job : Job m outs) (stack : Stack m outs final)
  | returned {outs : Ports (Ty V S)} (value : Tuple m.Val outs) (stack : Stack m outs final)

/-- Read the real graph's scoped wires at a binding. Invocation resolves the
linked callable and enters its body with fresh locals. Return binds the
result once, then resumes the saved suffix. θ jobs have no transition. -/
def State.next : State m outs → Option (State m outs)
  | .eval (.call callee arguments) stack => some (.eval (Job.openClosure m callee arguments) stack)
  | .eval (.region (.ret wires) entry locals) stack => some (.returned (wires.read entry locals) stack)
  | .eval (.region (.bind node children rest) entry locals) stack =>
    some (.eval (.node node.kind node.childSigs children (node.inputs.read entry locals))
      (.resume rest entry locals stack))
  | .eval (.node (.base (.simple (.primitive opcode))) _ _ input) stack =>
    some (.returned (m.primitive opcode input) stack)
  | .eval (.node (.base (.simple (.apply _))) _ _ (.cons callee arguments)) stack =>
    some (.eval (.call callee arguments) stack)
  | .eval (.node (.base (.gamma _)) _ children (.cons tag entry)) stack =>
    some (.eval (.region (children tag.selector) entry (PUnit.unit : Locals m.Val [])) stack)
  | .eval (.node (.theta _) _ _ _) _ | .eval (.iteration ..) _ => none
  | .returned value (.resume suffix entry locals outer) =>
    some (.eval (.region suffix entry (locals.snoc value)) outer)
  | .returned _ .halt => none

def State.result : State m outs → Option (Tuple m.Val outs)
  | .returned value .halt => some value
  | _ => none

def Step (source target : State m outs) : Prop :=
  source.next = some target

/-- An incomplete terminal state, such as an encountered θ vertex. -/
def State.Unsupported (state : State m outs) : Prop :=
  state.next = none ∧ state.result = none

/-- The run stays within the supported control fragment. This condition
only constrains selected γ arms and actual linked callees. -/
def Admitted (state : State m outs) : Prop :=
  ∀ reached, Relation.ReflTransGen Step state reached → ¬ reached.Unsupported

def Completes (state : State m outs) (output : Tuple m.Val outs) : Prop :=
  Relation.ReflTransGen Step state (.returned output .halt)

/-- Start the machine at a real recursive runtime job. -/
def start (job : Job m outs) : State m outs :=
  .eval job .halt

/-- Advance by at most the given number of transitions. A terminal state
is retained so completion and unsupported control can be inspected. -/
def State.runFor : Nat → State m outs → State m outs
  | 0, state => state
  | n + 1, state =>
    match state.next with
    | none => state
    | some target => runFor n target

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation
