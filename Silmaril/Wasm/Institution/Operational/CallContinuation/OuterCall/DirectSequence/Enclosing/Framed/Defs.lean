module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open StraightLine

/-- The checked body of an already-entered function, its label exit, and
the result delivered to the calling frame. -/
inductive State (ctx : Context) (site : Site) where
  | label (body : Enclosing.State ctx site)
  | exit (result : Nested.Result)
  | done (result : Nested.Result)

def Admitted {ctx : Context} {site : Site} : State ctx site → Prop
  | .label body => Enclosing.Admitted body
  | .exit r | .done r => Sequence.ResultTyped ctx.sequence r

inductive Unwinding (ctx : Context) (site : Site) : State ctx site → Prop where
  | label {body : Enclosing.State ctx site} (trap : Enclosing.Unwinding ctx site body) :
      Unwinding ctx site (.label body)
  | exit : Unwinding ctx site (.exit .trap)
  | done : Unwinding ctx site (.done .trap)

inductive Ground (ctx : Context) (site : Site) : State ctx site → State ctx site → Prop where
  | leaveLabel {a : Sequence.State ctx.sequence} {r : Nested.Result} (finished : Sequence.Finished ctx.sequence a r) :
      Ground ctx site (.label (.continuation a)) (.exit r)
  | leaveFrame (r : Nested.Result) (arity : Sequence.ResultArity ctx.sequence r) :
      Ground ctx site (.exit r) (.done r)

inductive Judgment (ctx : Context) (site : Site) where
  | body (judgment : Enclosing.Judgment ctx site)
  | step (a b : State ctx site)

inductive RuleInstance (ctx : Context) (p : Program) : Rule (Judgment ctx p.site) → Prop where
  | inherit {r : Rule (Enclosing.Judgment ctx p.site)} (rule : Enclosing.RuleInstance ctx p r) :
      RuleInstance ctx p ⟨r.premises.map .body, .body r.conclusion⟩
  | underLabel (a b : Enclosing.State ctx p.site) :
      RuleInstance ctx p ⟨[.body (.step a b)], .step (.label a) (.label b)⟩
  | ground {a b : State ctx p.site} (rule : Ground ctx p.site a b) :
      RuleInstance ctx p ⟨[], .step a b⟩

def shape (ctx : Context) (site : Site) : SOS.Shape.{0} :=
  ⟨⟨State ctx site, Unit⟩, Judgment ctx site, fun (a, _, b) => .step a b⟩

def presentation (ctx : Context) (p : Program) : SOS.Presentation := ⟨shape ctx p.site, {r | RuleInstance ctx p r}⟩

abbrev Edge (ctx : Context) (p : Program) (a b : State ctx p.site) := (presentation ctx p).Derives (.step a b)
abbrev Runs (ctx : Context) (p : Program) := Relation.ReflTransGen (Edge ctx p)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence.Enclosing.Framed
