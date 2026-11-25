module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Composed.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Execution.Runtime (FuncAddr Frame Value)
open OuterCall.Computed

structure Target where
  index : FuncIdx
  address : FuncAddr
  callee : CallFrame.Callee

/-- A finite table of direct-call targets in an entered, fixed caller frame. -/
structure Site where
  frame : Frame
  targets : List Target
  results : List NumType

abbrev Site.TargetId (site : Site) := Fin site.targets.length

def Site.target (site : Site) (i : site.TargetId) : Target := site.targets[i]

def Site.ReadOnly (site : Site) : Prop :=
  ∀ i : site.TargetId, OuterCall.Computed.Sequence.Composed.ReadOnly (site.target i).callee.program

def Site.TypedTargets (site : Site) : Prop :=
  ∀ i : site.TargetId, (site.target i).callee.program.Typed (site.target i).callee

inductive Op (site : Site) where
  | numeric (op : Prefix.Op)
  | call (target : site.TargetId)

/-- The checker reads types top-first. Runtime values are kept in evaluation order. -/
def checkOp (site : Site) (types : List NumType) : Op site → Option (List NumType)
  | .numeric op => Prefix.checkOp (site.frame.locals.map Value.type) types op
  | .call i =>
    let callee := (site.target i).callee
    if types.take callee.params.length = callee.params.reverse then
      some (callee.result.toList ++ types.drop callee.params.length)
    else none

def check (site : Site) (types : List NumType) : List (Op site) → Option (List NumType)
  | [] => some types
  | op :: rest => (checkOp site types op).bind fun next => check site next rest

def WellTyped (site : Site) (stack : List Value) (code : List (Op site)) : Prop :=
  check site (Prefix.stackTypes stack) code = some site.results.reverse

def ResumeTyped (site : Site) (i : site.TargetId) (saved : List Value) (rest : List (Op site)) : Prop :=
  check site ((site.target i).callee.result.toList ++ Prefix.stackTypes saved) rest = some site.results.reverse

inductive State (site : Site) where
  | running (stack : List Value) (rest : List (Op site))
  | active (i : site.TargetId) (callee : CallFrame.State) (rest : List (Op site))
  | trapped (stack : List Value) (rest : List (Op site))

/-- The administrative label can leave when its checked sequence has yielded
only values or a trap with no surrounding operands or pending instructions. -/
inductive Finished (site : Site) : State site → Nested.Result → Prop where
  | values (stack : List Value) : Finished site (.running stack []) (.values stack)
  | trap : Finished site (.trapped [] []) .trap

def ResultTyped (site : Site) : Nested.Result → Prop
  | .values stack => stack.map Value.type = site.results
  | .trap => True

def ResultArity (site : Site) : Nested.Result → Prop
  | .values stack => stack.length = site.results.length
  | .trap => True

def attach {site : Site} (i : site.TargetId) (rest : List (Op site)) : CallFrame.State → State site
  | .returned saved values => .running (saved ++ values) rest
  | .trapped saved => .trapped saved rest
  | phase => .active i phase rest

def afterOp {site : Site} (rest : List (Op site)) : Prefix.Outcome → State site
  | .values stack => .running stack rest
  | .trap stack => .trapped stack rest

def Admitted (site : Site) : State site → Prop
  | .running stack rest => WellTyped site stack rest
  | .active i phase rest =>
    Active phase ∧ CallFrame.Admitted (site.target i).callee phase ∧ ResumeTyped site i phase.saved rest
  | .trapped .. => True

inductive Ground (site : Site) : State site → State site → Prop where
  | numeric {stack : List Value} {op : Prefix.Op} {rest : List (Op site)} {out : Prefix.Outcome}
      (step : Prefix.Reduce site.frame.locals stack op out) :
      Ground site (.running stack (.numeric op :: rest)) (afterOp rest out)
  | resolve (i : site.TargetId) (saved args : List Value) (rest : List (Op site))
      (count : args.length = (site.target i).callee.params.length) :
      Ground site (.running (saved ++ args) (.call i :: rest)) (.active i (.invoke saved args) rest)
  | discard {stack kept : List Value} {before rest : List (Op site)}
      (step : Prefix.Discard stack before kept rest) :
      Ground site (.trapped stack before) (.trapped kept rest)

inductive Judgment (site : Site) where
  | callee (i : site.TargetId) (edge : CallFrame.Judgment)
  | step (a b : State site)

inductive RuleInstance (site : Site) : Rule (Judgment site) → Prop where
  | inherit (i : site.TargetId) {r : Rule CallFrame.Judgment}
      (rule : CallFrame.RuleInstance (site.target i).callee r) :
      RuleInstance site ⟨r.premises.map (.callee i), .callee i r.conclusion⟩
  | call (i : site.TargetId) (a b : CallFrame.State) (rest : List (Op site)) (live : Active a) :
      RuleInstance site ⟨[.callee i (.call a b)], .step (.active i a rest) (attach i rest b)⟩
  | ground {a b : State site} (rule : Ground site a b) : RuleInstance site ⟨[], .step a b⟩

def shape (site : Site) : SOS.Shape.{0} := ⟨⟨State site, Unit⟩, Judgment site, fun (a, _, b) => .step a b⟩

def presentation (site : Site) : SOS.Presentation := ⟨shape site, {r | RuleInstance site r}⟩

abbrev Edge (site : Site) (a b : State site) := (presentation site).Derives (.step a b)
abbrev Runs (site : Site) := Relation.ReflTransGen (Edge site)

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
