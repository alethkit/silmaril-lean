module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs

/-! Executable finite prefixes of the typed partial continuation machine. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {final : Ports (Ty V S)}

/-- A computable interpretation whose primitive actions may be undefined. -/
structure Actions (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) where
  step {ins outs : Ports (Ty V S)} :
    Op ins outs → Tuple m.Val ins → StateT σ Option (Tuple m.Val outs)

def Actions.toPrimitives (actions : Actions m σ) : Primitives m σ where
  step opcode input := fun store => _root_.Part.ofOption ((actions.step opcode input).run store)

/-- Run the original total primitives through the executable interface. -/
def Actions.liftTotal (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) : Actions m σ where
  step opcode input := fun store => some (m.primitive opcode input, store)

/-- A transition uses the same typed control, selected primitive and saved
stack as the partial continuation machine. -/
def next? (actions : Actions m σ) (source : Config m σ final) : Option (Config m σ final) :=
  match selectedPrimitive source.control with
  | some active =>
    ((actions.step active.site.opcode active.site.input).run source.store).map
      fun (output, store) => ⟨.returned output active.stack, store⟩
  | none => source.control.next.map fun next => ⟨next, source.store⟩

/-- Advance by at most the budgeted microsteps. Keep the exact terminal
configuration, or the live configuration for resumption at the budget. -/
def runFor (actions : Actions m σ) : Nat → Config m σ final → Config m σ final
  | 0, source => source
  | fuel + 1, source =>
    match next? actions source with
    | none => source
    | some next => runFor actions fuel next

inductive Observation (m : Machine.{u, v, w} Op) (σ : Type (max u v w)) (final : Ports (Ty V S)) where
  | returned (values : Tuple m.Val final) (store : σ)
  | blocked (active : ActivePrimitive m final) (store : σ)
  | suspended (configuration : Config m σ final)

/-- Inspect the configuration at the budget boundary. A blocked endpoint
records the attempted action, its typed operands and live stack. -/
def observe (actions : Actions m σ) (source : Config m σ final) : Observation m σ final :=
  match source.result with
  | some (values, store) => .returned values store
  | none =>
    match selectedPrimitive source.control with
    | none => .suspended source
    | some active =>
      match (actions.step active.site.opcode active.site.input).run source.store with
      | none => .blocked active source.store
      | some _ => .suspended source

/-- Execute a finite prefix of a fresh typed job, including a call to a
linked export. The budget is on machine transitions, independent of call
depth and the number of θ activations. -/
def run (actions : Actions m σ) (fuel : Nat) (job : Job m final) (store : σ) : Observation m σ final :=
  observe actions (runFor actions fuel ⟨start job, store⟩)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Executable
