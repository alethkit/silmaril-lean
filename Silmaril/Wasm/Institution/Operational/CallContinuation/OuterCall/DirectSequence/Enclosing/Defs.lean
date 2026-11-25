module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Frame Value)
open StraightLine

/-- A checked sequence in the already-entered enclosing frame. Its target table
and result types are independent of the targets inside the outer invocation. -/
structure Context where
  sequence : Sequence.Site
  saved : List Value
  continuation : List (Sequence.Op sequence)

def Context.frame (ctx : Context) : Frame := ctx.sequence.frame

/-- The local-read and integer-only profile is the empty-target specialization. -/
def Context.numeric (frame : Frame) (saved : List Value) (code : List Computed.Prefix.Op)
    (results : List NumType) : Context :=
  ⟨⟨frame, [], results⟩, saved, code.map .numeric⟩

def Context.Typed (ctx : Context) (p : Program) : Prop :=
  Sequence.check ctx.sequence (p.site.result.toList.reverse ++ Computed.Prefix.stackTypes ctx.saved)
    ctx.continuation = some ctx.sequence.results.reverse

def Live {site : Site} : DirectSequence.State site → Prop
  | .done _ => False
  | _ => True

inductive State (ctx : Context) (site : Site) where
  | active (phase : DirectSequence.State site)
  | continuation (phase : Sequence.State ctx.sequence)

abbrev State.resume {ctx : Context} {site : Site}
    (stack : List Value) (rest : List (Sequence.Op ctx.sequence)) : State ctx site :=
  .continuation (.running stack rest)

abbrev State.trapped {ctx : Context} {site : Site}
    (stack : List Value) (rest : List (Sequence.Op ctx.sequence)) : State ctx site :=
  .continuation (.trapped stack rest)

def attach {site : Site} (ctx : Context) : DirectSequence.State site → State ctx site
  | .done (.values stack) => .resume (ctx.saved ++ stack) ctx.continuation
  | .done .trap => .trapped ctx.saved ctx.continuation
  | phase => .active phase

inductive Unwinding (ctx : Context) (site : Site) : State ctx site → Prop where
  | active {phase : DirectSequence.State site} (trap : DirectSequence.Unwinding site phase) (live : Live phase) :
      Unwinding ctx site (.active phase)
  | trapped (stack : List Value) (rest : List (Sequence.Op ctx.sequence)) : Unwinding ctx site (.trapped stack rest)

def Admitted {ctx : Context} {site : Site} : State ctx site → Prop
  | .active phase => Live phase ∧ DirectSequence.Admitted site phase
  | .continuation phase => Sequence.Admitted ctx.sequence phase

inductive Judgment (ctx : Context) (site : Site) where
  | invocation (judgment : DirectSequence.Judgment site)
  | suffix (judgment : Sequence.Judgment ctx.sequence)
  | step (source target : State ctx site)

inductive RuleInstance (ctx : Context) (p : Program) : Rule (Judgment ctx p.site) → Prop where
  | inheritInvocation {r : Rule (DirectSequence.Judgment p.site)} (rule : DirectSequence.RuleInstance p r) :
      RuleInstance ctx p ⟨r.premises.map .invocation, .invocation r.conclusion⟩
  | inheritSuffix {r : Rule (Sequence.Judgment ctx.sequence)} (rule : Sequence.RuleInstance ctx.sequence r) :
      RuleInstance ctx p ⟨r.premises.map .suffix, .suffix r.conclusion⟩
  | invoke {a : DirectSequence.State p.site} (b : DirectSequence.State p.site) (live : Live a) :
      RuleInstance ctx p ⟨[.invocation (.step a b)], .step (.active a) (attach ctx b)⟩
  | resume (a b : Sequence.State ctx.sequence) :
      RuleInstance ctx p ⟨[.suffix (.step a b)], .step (.continuation a) (.continuation b)⟩

def shape (ctx : Context) (site : Site) : SOS.Shape.{0} := ⟨⟨State ctx site, Unit⟩, Judgment ctx site, fun (a, _, b) => .step a b⟩
def presentation (ctx : Context) (p : Program) : SOS.Presentation := ⟨shape ctx p.site, {r | RuleInstance ctx p r}⟩

abbrev Edge (ctx : Context) (p : Program) (a b : State ctx p.site) := (presentation ctx p).Derives (.step a b)
abbrev Runs (ctx : Context) (p : Program) := Relation.ReflTransGen (Edge ctx p)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing
