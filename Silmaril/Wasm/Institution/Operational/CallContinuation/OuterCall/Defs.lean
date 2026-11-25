module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (FuncAddr Value ModuleInst)

/-!
# Typed outer invocation followed by one nested call

The outer body supplies numeric literal arguments to a distinct allocated inner
function and has one pending `nop`. The outer signature uses the inner result
type. At the top level the caller supplies exactly the typed arguments, with no
saved operands or pending instruction. The inner callee follows the existing
typed call guard.
-/

structure Outer where
  moduleInst : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  innerIndex : FuncIdx
  innerArgs : List Value
  inner : CallFrame.Callee

def Outer.arity (fn : Outer) := fn.inner.arity

structure CallSite where
  outerIndex : FuncIdx
  outerAddr : FuncAddr
  innerAddr : FuncAddr
  args : List Value
  callee : Outer

inductive State where
  | call
  | invoke
  | entered
  | nested (phase : Nested.State)

def CallSite.start (site : CallSite) : Nested.State :=
  .label (.active (.invoke [] site.callee.innerArgs))

def Admitted (site : CallSite) : State → Prop
  | .nested phase => Nested.Admitted site.callee.inner phase
  | _ => True

structure Typed (site : CallSite) : Prop where
  outerArgs : site.args.map Value.type = site.callee.params
  innerArgs : site.callee.innerArgs.map Value.type = site.callee.inner.params
  body : site.callee.inner.program.Typed site.callee.inner
  nonRecursive : site.outerAddr ≠ site.innerAddr

inductive Judgment where
  | nested (edge : Nested.Judgment)
  | transition (a b : State)

inductive Ground (site : CallSite) : State → State → Prop where
  | resolve : Ground site .call .invoke
  | enter : Ground site .invoke .entered
  | resolveInner : Ground site .entered (.nested site.start)

inductive RuleInstance (site : CallSite) : Rule Judgment → Prop where
  | inherit {r : Rule Nested.Judgment} (rule : Nested.RuleInstance site.callee.inner site.callee.arity r) :
      RuleInstance site ⟨r.premises.map .nested, .nested r.conclusion⟩
  | delegate (a b : Nested.State) :
      RuleInstance site ⟨[.nested (.step a b)], .transition (.nested a) (.nested b)⟩
  | ground {a b : State} (rule : Ground site a b) : RuleInstance site ⟨[], .transition a b⟩

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => .transition a b⟩
def presentation (site : CallSite) : SOS.Presentation := ⟨shape, {r | RuleInstance site r}⟩
abbrev Edge (site : CallSite) (a b : State) := (presentation site).Derives (.transition a b)
abbrev Runs (site : CallSite) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall
