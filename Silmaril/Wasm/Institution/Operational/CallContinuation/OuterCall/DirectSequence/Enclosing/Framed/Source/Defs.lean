module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Declaration.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Value)
open StraightLine

/-- The source body supplies a literal operand prefix to a checked invocation
and continues with a checked direct-call sequence. The targets and instructions
are static, independently of the arguments of this function. -/
structure Body (decl : Declaration) where
  invocation : DirectSequence.Program
  saved : List Value
  targets : List Sequence.Target
  continuation : List (Sequence.Op ⟨decl.frame [], targets, decl.results⟩)

def Body.site {decl : Declaration} (body : Body decl) (args : List Value) : Sequence.Site :=
  ⟨decl.frame args, body.targets, decl.results⟩

def Body.context {decl : Declaration} (body : Body decl) (args : List Value) : Enclosing.Context :=
  ⟨body.site args, body.saved, body.continuation.map fun
    | .numeric op => .numeric op
    | .call target => .call target⟩

structure Invocation where
  target : CallTarget
  body : Body target.declaration
  args : List Value

def Invocation.context (call : Invocation) : Enclosing.Context := call.body.context call.args

def Invocation.start (call : Invocation) : Framed.State call.context call.body.invocation.site :=
  .label (.active .call)

structure Typed (call : Invocation) : Prop where
  args : call.args.map Value.type = call.target.declaration.params
  continuation : call.context.Typed call.body.invocation

inductive State (call : Invocation) where
  | call
  | invoke
  | framed (phase : Framed.State call.context call.body.invocation.site)

def Admitted {call : Invocation} : State call → Prop
  | .framed phase => Framed.Admitted phase
  | _ => True

inductive Ground (call : Invocation) : State call → State call → Prop where
  | resolve : Ground call .call .invoke
  | enter : Ground call .invoke (.framed call.start)

inductive Judgment (call : Invocation) where
  | body (judgment : Framed.Judgment call.context call.body.invocation.site)
  | step (a b : State call)

inductive RuleInstance (call : Invocation) : Rule (Judgment call) → Prop where
  | inherit {r : Rule (Framed.Judgment call.context call.body.invocation.site)}
      (rule : Framed.RuleInstance call.context call.body.invocation r) :
      RuleInstance call ⟨r.premises.map .body, .body r.conclusion⟩
  | framed (a b : Framed.State call.context call.body.invocation.site) :
      RuleInstance call ⟨[.body (.step a b)], .step (.framed a) (.framed b)⟩
  | ground {a b : State call} (rule : Ground call a b) :
      RuleInstance call ⟨[], .step a b⟩

def shape (call : Invocation) : SOS.Shape.{0} :=
  ⟨⟨State call, Unit⟩, Judgment call, fun (a, _, b) => .step a b⟩

def presentation (call : Invocation) : SOS.Presentation := ⟨shape call, {r | RuleInstance call r}⟩

abbrev Edge (call : Invocation) (a b : State call) := (presentation call).Derives (.step a b)
abbrev Runs (call : Invocation) := Relation.ReflTransGen (Edge call)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed.Source
