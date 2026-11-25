module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Frame Value FuncAddr)
open OuterCall.Computed

/-- A direct inner call in an entered outer frame and label. The continuation
uses the shared local-read and integer-binary instruction grammar. -/
structure Site where
  outer : Frame
  index : FuncIdx
  address : FuncAddr
  callee : CallFrame.Callee
  continuation : List Prefix.Op
  result : Option NumType

def Site.arity (site : Site) : Nat := site.result.toList.length

def Site.ResumeTyped (site : Site) (saved : List Value) : Prop :=
  Prefix.check (site.outer.locals.map Value.type)
    (site.callee.result.toList ++ Prefix.stackTypes saved) site.continuation = some site.result.toList.reverse

inductive State where
  | call (saved args : List Value)
  | active (callee : CallFrame.State)
  | resume (stack : List Value) (rest : List Prefix.Op)
  | trapped (stack : List Value) (rest : List Prefix.Op)
  | boundary (phase : Nested.State)

def resumed (stack : List Value) : List Prefix.Op → State
  | [] => .boundary (.label (.done stack))
  | todo => .resume stack todo

def trapped (stack : List Value) (rest : List Prefix.Op) : State :=
  match stack, rest with
  | [], [] => .boundary (.label (.trapped [] false))
  | stack, rest => .trapped stack rest

def attach (site : Site) : CallFrame.State → State
  | .returned saved results => resumed (saved ++ results) site.continuation
  | .trapped saved => trapped saved site.continuation
  | q => .active q

def afterOp (rest : List Prefix.Op) : Prefix.Outcome → State
  | .values stack => resumed stack rest
  | .trap saved => trapped saved rest

def BoundaryTyped (result : List NumType) : Nested.State → Prop
  | .label (.done stack) | .exit (.values stack) | .done (.values stack) =>
    stack.map Value.type = result
  | .label (.trapped [] false) | .exit .trap | .done .trap => True
  | _ => False

/-- The trapped body and its administrative exits through the outer label and frame. -/
def Unwinding : State → Prop
  | .trapped .. | .boundary (.label (.trapped [] false))
  | .boundary (.exit .trap) | .boundary (.done .trap) => True
  | _ => False

def Admitted (site : Site) : State → Prop
  | .call saved args => CallFrame.Admitted site.callee (.invoke saved args) ∧ site.ResumeTyped saved
  | .active q => Active q ∧ CallFrame.Admitted site.callee q ∧ site.ResumeTyped q.saved
  | .resume stack rest => rest ≠ [] ∧ Prefix.WellTyped site.outer.locals stack rest site.result.toList
  | .trapped stack rest => stack ≠ [] ∨ rest ≠ []
  | .boundary q => BoundaryTyped site.result.toList q

inductive Ground (site : Site) : State → State → Prop where
  | resolve (saved args : List Value) : Ground site (.call saved args) (.active (.invoke saved args))
  | resume {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op} {ans : Prefix.Outcome}
      (step : Prefix.Reduce site.outer.locals stack op ans) :
      Ground site (.resume stack (op :: rest)) (afterOp rest ans)
  | discard {stack kept : List Value} {before rest : List Prefix.Op}
      (step : Prefix.Discard stack before kept rest) :
      Ground site (.trapped stack before) (trapped kept rest)
  | boundary {a b : Nested.State} (step : Nested.Ground site.arity a b) :
      Ground site (.boundary a) (.boundary b)

inductive Judgment where
  | inner (edge : CallFrame.Judgment)
  | step (a b : State)

inductive RuleInstance (site : Site) : Rule Judgment → Prop where
  | inner {r : Rule CallFrame.Judgment} (rule : CallFrame.RuleInstance site.callee r) :
      RuleInstance site ⟨r.premises.map .inner, .inner r.conclusion⟩
  | call (a b : CallFrame.State) (live : Active a) :
      RuleInstance site ⟨[.inner (.call a b)], .step (.active a) (attach site b)⟩
  | ground {a b : State} (rule : Ground site a b) : RuleInstance site ⟨[], .step a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .step a b⟩
def presentation (site : Site) : SOS.Presentation := ⟨shape, {r | RuleInstance site r}⟩
abbrev Edge (site : Site) (a b : State) := (presentation site).Derives (.step a b)
abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine
