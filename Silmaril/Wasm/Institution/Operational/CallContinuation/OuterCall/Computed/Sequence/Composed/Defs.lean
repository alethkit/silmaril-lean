module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Value)

/-- An ordinary outer invocation evaluates its argument prefix, calls a distinct
inner callee, and resumes a checked straight-line continuation. -/
structure Site extends Sequence.Site where
  continuation : List Prefix.Op
  result : Option NumType

def Site.innerSite (site : Site) : StraightLine.Site :=
  ⟨site.toSite.frame, site.innerIndex, site.innerAddr, site.inner, site.continuation, site.result⟩

/-- The source callee uses only reads, constants, return, or unreachable. -/
def ReadOnly : CallFrame.Program → Prop
  | .locals code => ∀ i, Locals.Op.set i ∉ code ∧ Locals.Op.tee i ∉ code
  | .ret _ | .unreachable => True

structure Typed (site : Site) : Prop extends Sequence.Typed site.toSite where
  continuationTyped : site.innerSite.ResumeTyped []
  innerReadOnly : ReadOnly site.inner.program

inductive Pending where
  | op (op : Prefix.Op)
  | call

def Site.pending (site : Site) (remaining : List Prefix.Op) : List Pending :=
  remaining.map .op ++ .call :: site.continuation.map .op

inductive State where
  | call
  | invoke
  | args (stack : List Value) (remaining : List Prefix.Op)
  | argumentTrap (stack : List Value) (remaining : List Pending)
  | inner (phase : StraightLine.State)

/-- The empty prefix is already the direct inner-call state. -/
def evaluating (stack : List Value) : List Prefix.Op → State
  | [] => .inner (.call [] stack)
  | remaining => .args stack remaining

def argumentTrap (stack : List Value) (remaining : List Pending) : State :=
  match stack, remaining with
  | [], [] => .inner (StraightLine.trapped [] [])
  | stack, remaining => .argumentTrap stack remaining

def afterArg (site : Site) (remaining : List Prefix.Op) : Prefix.Outcome → State
  | .values stack => evaluating stack remaining
  | .trap saved => .argumentTrap saved (site.pending remaining)

def Admitted (site : Site) : State → Prop
  | .args stack remaining =>
    remaining ≠ [] ∧ Prefix.WellTyped site.toSite.frame.locals stack remaining site.inner.params
  | .argumentTrap stack remaining => stack ≠ [] ∨ remaining ≠ []
  | .inner phase => StraightLine.Admitted site.innerSite phase
  | _ => True

inductive Ground (site : Site) : State → State → Prop where
  | resolve : Ground site .call .invoke
  | enter : Ground site .invoke (evaluating [] site.prefixCode)
  | evaluate {stack : List Value} {op : Prefix.Op} {remaining : List Prefix.Op} {out : Prefix.Outcome}
      (step : Prefix.Reduce site.toSite.frame.locals stack op out) :
      Ground site (.args stack (op :: remaining)) (afterArg site remaining out)
  | discard {stack kept : List Value} {before remaining : List Pending}
      (step : Prefix.Discard stack before kept remaining) :
      Ground site (.argumentTrap stack before) (argumentTrap kept remaining)

inductive Judgment where
  | inner (edge : StraightLine.Judgment)
  | step (a b : State)

inductive RuleInstance (site : Site) : Rule Judgment → Prop where
  | inherit {r : Rule StraightLine.Judgment} (rule : StraightLine.RuleInstance site.innerSite r) :
      RuleInstance site ⟨r.premises.map .inner, .inner r.conclusion⟩
  | delegate (a b : StraightLine.State) :
      RuleInstance site ⟨[.inner (.step a b)], .step (.inner a) (.inner b)⟩
  | ground {a b : State} (rule : Ground site a b) : RuleInstance site ⟨[], .step a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .step a b⟩

def presentation (site : Site) : SOS.Presentation := ⟨shape, {r | RuleInstance site r}⟩

abbrev Edge (site : Site) (a b : State) := (presentation site).Derives (.step a b)
abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed
