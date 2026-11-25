module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Declaration.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (Frame FuncAddr ModuleInst Value)

open StraightLine

/-- A direct outer call with exact numeric arguments and an optional numeric result. -/
structure Site where
  index : FuncIdx
  address : FuncAddr
  args : List Value
  module : ModuleInst
  typeIndex : TypeIdx
  params : List NumType
  locals : List NumType
  result : Option NumType
  targets : List Sequence.Target

def Site.callTarget (site : Site) : CallTarget :=
  ⟨site.index, site.address, ⟨site.module, site.typeIndex, site.params, site.locals, site.result.toList⟩⟩

def Site.frame (site : Site) : Frame := site.callTarget.declaration.frame site.args
def Site.arity (site : Site) : Nat := site.result.toList.length
def Site.body (site : Site) : Sequence.Site := ⟨site.frame, site.targets, site.result.toList⟩

/-- Outer function code, indexed by the initialized frame and finite target table. -/
structure Program where
  site : Site
  code : List (Sequence.Op site.body)

structure Typed (p : Program) : Prop where
  args : p.site.args.map Value.type = p.site.params
  body : Sequence.WellTyped p.site.body [] p.code
  distinct : ∀ i : p.site.body.TargetId, (p.site.body.target i).address ≠ p.site.address

inductive State (site : Site) where
  | call
  | invoke
  | label (body : Sequence.State site.body)
  | exit (result : Nested.Result)
  | done (result : Nested.Result)

inductive Unwinding (site : Site) : State site → Prop where
  | label (stack : List Value) (rest : List (Sequence.Op site.body)) :
      Unwinding site (.label (.trapped stack rest))
  | exit : Unwinding site (.exit .trap)
  | done : Unwinding site (.done .trap)

def ResultTyped (site : Site) : Nested.Result → Prop
  | .values stack => stack.map Value.type = site.result.toList
  | .trap => True

def ResultArity (site : Site) : Nested.Result → Prop
  | .values stack => stack.length = site.arity
  | .trap => True

def Admitted (site : Site) : State site → Prop
  | .label body => Sequence.Admitted site.body body
  | .exit result | .done result => ResultTyped site result
  | _ => True

/-- The two fully evaluated bodies that may leave the function's label. -/
inductive Finished (site : Site) : Sequence.State site.body → Nested.Result → Prop where
  | values (stack : List Value) : Finished site (.running stack []) (.values stack)
  | trap : Finished site (.trapped [] []) .trap

inductive Ground (p : Program) : State p.site → State p.site → Prop where
  | resolve : Ground p .call .invoke
  | enter : Ground p .invoke (.label (.running [] p.code))
  | leaveLabel {body result} (finished : Finished p.site body result) :
      Ground p (.label body) (.exit result)
  | leaveFrame (result : Nested.Result) (arity : ResultArity p.site result) :
      Ground p (.exit result) (.done result)

inductive Judgment (site : Site) where
  | body (judgment : Sequence.Judgment site.body)
  | step (source target : State site)

inductive RuleInstance (p : Program) : Rule (Judgment p.site) → Prop where
  | inherit {r : Rule (Sequence.Judgment p.site.body)} (rule : Sequence.RuleInstance p.site.body r) :
      RuleInstance p ⟨r.premises.map .body, .body r.conclusion⟩
  | underLabel (a b : Sequence.State p.site.body) :
      RuleInstance p ⟨[.body (.step a b)], .step (.label a) (.label b)⟩
  | ground {a b : State p.site} (rule : Ground p a b) :
      RuleInstance p ⟨[], .step a b⟩

def shape (site : Site) : SOS.Shape.{0} := ⟨⟨State site, Unit⟩, Judgment site, fun (a, _, b) => .step a b⟩
def presentation (p : Program) : SOS.Presentation := ⟨shape p.site, {r | RuleInstance p r}⟩

abbrev Edge (p : Program) (a b : State p.site) := (presentation p).Derives (.step a b)
abbrev Runs (p : Program) := Relation.ReflTransGen (Edge p)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.DirectSequence
