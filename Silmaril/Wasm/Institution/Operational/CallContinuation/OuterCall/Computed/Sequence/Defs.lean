module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (FuncAddr Value ModuleInst Frame)

/-- An ordinary outer invocation computes its inner arguments with a finite
prefix. The rest of its body is one direct call followed by one `nop`. -/
structure Site where
  outerIndex : FuncIdx
  outerAddr : FuncAddr
  innerAddr : FuncAddr
  args : List Value
  outerModule : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  innerIndex : FuncIdx
  inner : CallFrame.Callee
  prefixCode : List Prefix.Op

def Site.arity (site : Site) := site.inner.arity

def Site.frame (site : Site) : Frame :=
  ⟨site.args ++ site.locals.map Value.zero, site.outerModule⟩

structure Typed (site : Site) : Prop where
  outerArgs : site.args.map Value.type = site.params
  prefixTyped : Prefix.WellTyped site.frame.locals [] site.prefixCode site.inner.params
  innerBody : site.inner.program.Typed site.inner
  nonRecursive : site.outerAddr ≠ site.innerAddr

/-- Instructions that can remain after an early trap. One cut rule
handles both pending argument evaluation and the call suffix. -/
inductive Pending where
  | arg (op : Prefix.Op)
  | call
  | nop

def pending (rest : List Prefix.Op) : List Pending := rest.map .arg ++ [.call, .nop]

inductive State where
  | call
  | invoke
  | args (stack : List Value) (rest : List Prefix.Op)
  | trap (stack : List Value) (rest : List Pending)
  | nested (phase : Nested.State)

def poppedTrap : State := .nested (.label (.trapped [] false))

/-- At the isolated trap the existing nested SOS handles the label and frame exits. -/
def trapState (stack : List Value) (rest : List Pending) : State :=
  match stack, rest with
  | [], [] => poppedTrap
  | stack, rest => .trap stack rest

def innerStart (stack : List Value) : Nested.State :=
  .label (.active (.invoke [] stack))

def afterOp (rest : List Prefix.Op) : Prefix.Outcome → State
  | .values stack => .args stack rest
  | .trap saved => .trap saved (pending rest)

def Admitted (site : Site) : State → Prop
  | .args stack rest => Prefix.WellTyped site.frame.locals stack rest site.inner.params
  | .trap stack rest => stack ≠ [] ∨ rest ≠ []
  | .nested phase => Nested.Admitted site.inner phase
  | _ => True

inductive Ground (site : Site) : State → State → Prop where
  | resolve : Ground site .call .invoke
  | enter : Ground site .invoke (.args [] site.prefixCode)
  | arg {stack next : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
      (step : Prefix.Reduce site.frame.locals stack op (.values next)) :
      Ground site (.args stack (op :: rest)) (.args next rest)
  | trap {stack saved : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
      (step : Prefix.Reduce site.frame.locals stack op (.trap saved)) :
      Ground site (.args stack (op :: rest)) (.trap saved (pending rest))
  | discard {stack kept : List Value} {before rest : List Pending}
      (step : Prefix.Discard stack before kept rest) :
      Ground site (.trap stack before) (trapState kept rest)
  | resolveInner (stack : List Value) :
      Ground site (.args stack []) (.nested (innerStart stack))

inductive Judgment where
  | nested (edge : Nested.Judgment)
  | step (a b : State)

inductive RuleInstance (site : Site) : Rule Judgment → Prop where
  | inherit {r : Rule Nested.Judgment} (rule : Nested.RuleInstance site.inner site.arity r) :
      RuleInstance site ⟨r.premises.map .nested, .nested r.conclusion⟩
  | delegate (a b : Nested.State) :
      RuleInstance site ⟨[.nested (.step a b)], .step (.nested a) (.nested b)⟩
  | ground {a b : State} (rule : Ground site a b) :
      RuleInstance site ⟨[], .step a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .step a b⟩
def presentation (site : Site) : SOS.Presentation := ⟨shape, {r | RuleInstance site r}⟩

abbrev Edge (site : Site) (a b : State) := (presentation site).Derives (.step a b)
abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence
