module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Frame Value)

/-- The already-entered enclosing frame and its saved operands and checked suffix. -/
structure Context where
  frame : Frame
  saved : List Value
  continuation : List Computed.Prefix.Op
  results : List NumType

def Context.Typed (ctx : Context) (p : Program) : Prop :=
  Computed.Prefix.check (ctx.frame.locals.map Value.type)
    (p.site.result.toList.reverse ++ Computed.Prefix.stackTypes ctx.saved) ctx.continuation = some ctx.results.reverse

def Live {site : Site} : DirectSequence.State site → Prop
  | .done _ => False
  | _ => True

inductive State (site : Site) where
  | active (phase : DirectSequence.State site)
  | resume (stack : List Value) (rest : List Computed.Prefix.Op)
  | trapped (stack : List Value) (rest : List Computed.Prefix.Op)

def attach {site : Site} (ctx : Context) : DirectSequence.State site → State site
  | .done (.values stack) => .resume (ctx.saved ++ stack) ctx.continuation
  | .done .trap => .trapped ctx.saved ctx.continuation
  | phase => .active phase

inductive Unwinding (site : Site) : State site → Prop where
  | active {phase : DirectSequence.State site} (trap : DirectSequence.Unwinding site phase) (live : Live phase) :
      Unwinding site (.active phase)
  | trapped (stack : List Value) (rest : List Computed.Prefix.Op) : Unwinding site (.trapped stack rest)

def afterOp {site : Site} (rest : List Computed.Prefix.Op) : Computed.Prefix.Outcome → State site
  | .values stack => .resume stack rest
  | .trap stack => .trapped stack rest

def Admitted {site : Site} (ctx : Context) : State site → Prop
  | .active phase => Live phase ∧ DirectSequence.Admitted site phase
  | .resume stack rest => Computed.Prefix.WellTyped ctx.frame.locals stack rest ctx.results
  | .trapped .. => True

inductive Ground (ctx : Context) (site : Site) : State site → State site → Prop where
  | resume {stack op rest out} (step : Computed.Prefix.Reduce ctx.frame.locals stack op out) :
      Ground ctx site (.resume stack (op :: rest)) (afterOp rest out)
  | discard {stack kept before rest} (step : Computed.Prefix.Discard stack before kept rest) :
      Ground ctx site (.trapped stack before) (.trapped kept rest)

inductive Judgment (site : Site) where
  | invocation (judgment : DirectSequence.Judgment site)
  | step (source target : State site)

inductive RuleInstance (ctx : Context) (p : Program) : Rule (Judgment p.site) → Prop where
  | inherit {r : Rule (DirectSequence.Judgment p.site)} (rule : DirectSequence.RuleInstance p r) :
      RuleInstance ctx p ⟨r.premises.map .invocation, .invocation r.conclusion⟩
  | invoke {a : DirectSequence.State p.site} (b : DirectSequence.State p.site) (live : Live a) :
      RuleInstance ctx p ⟨[.invocation (.step a b)], .step (.active a) (attach ctx b)⟩
  | ground {a b : State p.site} (rule : Ground ctx p.site a b) :
      RuleInstance ctx p ⟨[], .step a b⟩

def shape (site : Site) : SOS.Shape.{0} := ⟨⟨State site, Unit⟩, Judgment site, fun (a, _, b) => .step a b⟩
def presentation (ctx : Context) (p : Program) : SOS.Presentation := ⟨shape p.site, {r | RuleInstance ctx p r}⟩

abbrev Edge (ctx : Context) (p : Program) (a b : State p.site) := (presentation ctx p).Derives (.step a b)
abbrev Runs (ctx : Context) (p : Program) := Relation.ReflTransGen (Edge ctx p)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
