module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume

open Execution
open Execution.Runtime (Frame Value)
open CallContinuation.OuterCall
open CallContinuation
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

/-- A branch-free arm tail stores the ordered results and any saved site
operands in typed locals. The arm is void, so the writes exhaust its stack.
The function tail outside the loop retains the ordinary graph grammar. -/
structure Writes (entry : Entry) (saved : List Value) (results : List NumType) where
  indices : List LocalIdx
  source : entry.insideTail = indices.map Graph.Op.set
  typed : Locals.check entry.owner.localTypes (results.reverse ++ Prefix.stackTypes saved)
    (indices.map Locals.Op.set) = some []

inductive Phase (A : Type) where
  | write (locals stack : List Value) (indices : List LocalIdx)
  | armTrap (locals stack : List Value) (pending : List A)
  | loop (locals : List Value) (trapped : Bool)
  | caller (locals : List Value) (trapped : Bool)

def Phase.Live {A : Type} : Phase A → Prop
  | .caller .. => False
  | _ => True

/-- The arm and loop each exit in one step. A trap can first discard
operands or pending instructions in the arm. Once the loop exits, both
outcomes enter the existing function graph. -/
inductive Edge {A : Type} : Phase A → Phase A → Prop where
  | write {locals next stack saved value i rest} (split : stack = saved ++ [value])
      (step : Locals.Edge ⟨locals, [.value value, .set i]⟩ ⟨next, []⟩) :
      Edge (.write locals stack (i :: rest)) (.write next saved rest)
  | leaveArm (locals : List Value) : Edge (.write locals [] []) (.loop locals false)
  | discard {locals stack pending kept rest} (cut : Prefix.Discard stack pending kept rest) :
      Edge (.armTrap locals stack pending) (.armTrap locals kept rest)
  | leaveTrapArm (locals : List Value) : Edge (.armTrap locals [] []) (.loop locals true)
  | leaveLoop (locals : List Value) (trapped : Bool) : Edge (.loop locals trapped) (.caller locals trapped)

abbrev Runs {A : Type} := Relation.ReflTransGen (@Edge A)

def entryPhase (entry : Entry) (locals : List Value) (trapped : Bool) : Graph.Phase :=
  if trapped then .label locals (.trapped entry.owner.initial entry.tail) else entry.callerPhase locals

def delivery {A : Type} (caller : Frame) (saved : List Value) (indices : List LocalIdx)
    (pending : List A) : Nested.Result → Phase A
  | .values xs => .write caller.locals (saved ++ xs) indices
  | .trap => .armTrap caller.locals saved pending

def Admitted {A : Type} (entry : Entry) : Phase A → Prop
  | .write locals stack indices => locals.map Value.type = entry.owner.localTypes ∧
      Locals.check entry.owner.localTypes (Prefix.stackTypes stack) (indices.map Locals.Op.set) = some []
  | .armTrap locals .. | .loop locals _ | .caller locals _ => locals.map Value.type = entry.owner.localTypes

def corePhase {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame) : Phase Core.Admin → Core.Config H
  | .write locals stack indices =>
      entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore,
        coreValues stack ++ indices.map (fun i => .plain (.localSet i))⟩
  | .armTrap locals stack pending =>
      entry.coreArmWrap outer ⟨s, (entry.frame locals).toCore, coreValues stack ++ .trap :: pending⟩
  | .loop locals trapped =>
      entry.coreLoopWrap outer ⟨s, (entry.frame locals).toCore, if trapped then [.trap] else []⟩
  | .caller locals trapped => Graph.coreConfig s outer entry.cont.target (entryPhase entry locals trapped)

open Wasm.Lime1.Execution in
def limePhase {H : Type} (entry : Entry) (s : Store H) (outer : Frame) : Phase Admin → Config H
  | .write locals stack indices =>
      entry.limeArmWrap outer ⟨s, entry.frame locals,
        values stack ++ indices.map (fun i => .source (.localSet i))⟩
  | .armTrap locals stack pending =>
      entry.limeArmWrap outer ⟨s, entry.frame locals, values stack ++ .trap :: pending⟩
  | .loop locals trapped =>
      entry.limeLoopWrap outer ⟨s, entry.frame locals, if trapped then [.trap] else []⟩
  | .caller locals trapped => Graph.limeConfig s outer entry.cont.target (entryPhase entry locals trapped)

def coreCallee {H : Type} (entry : Entry) (s : Core.Store H) (outer : Frame)
    (call : Context.Invocation) (phase : Graph.Phase) : Core.Config H :=
  entry.coreArmWrap outer (call.coreCallee s (entry.insideTail.map Graph.coreEmit) phase)

open Wasm.Lime1.Execution in
def limeCallee {H : Type} (entry : Entry) (s : Store H) (outer : Frame)
    (call : Context.Invocation) (phase : Graph.Phase) : Config H :=
  entry.limeArmWrap outer (call.limeCallee s (entry.insideTail.map Graph.limeEmit) phase)

def Finish {A C : Type} (entry : Entry) (program : Graph.Program) (render : Phase A → C)
    (caller : Graph.Phase → C) (start : Phase A) (dst : C) : Prop :=
  (∃ phase, Runs start phase ∧ dst = render phase) ∨
  (∃ locals trapped, Runs start (.caller locals trapped) ∧
    ∃ phase, program.FrameRuns entry.address (entryPhase entry locals trapped) phase ∧ dst = caller phase)

def CalleeFinish {C : Type} (program : Graph.Program) (call : Context.Invocation)
    (render : Graph.Phase → C) (finish : Nested.Result → C → Prop) (dst : C) : Prop :=
  (∃ phase, program.FrameRuns call.address call.entered phase ∧ dst = render phase) ∨
  (∃ result, program.FrameRuns call.address call.entered (.done result) ∧ finish result dst)

def coreTrap (entry : Entry) (active : Source.Activation) (out : Outcome) : Phase Core.Admin :=
  let pending := match out with
    | .bounds => [active.binding.site.coreCast, active.binding.site.coreCall]
    | .mismatch _ => [active.binding.site.coreCall]
    | _ => []
  .armTrap active.caller.locals (active.operands.saved ++ active.operands.args) (pending ++ entry.insideTail.map Graph.coreEmit)

def limeTrap (entry : Entry) (active : Source.Activation) : Phase Wasm.Lime1.Execution.Admin :=
  .armTrap active.caller.locals (active.operands.saved ++ active.operands.args) (entry.insideTail.map Graph.limeEmit)

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume
