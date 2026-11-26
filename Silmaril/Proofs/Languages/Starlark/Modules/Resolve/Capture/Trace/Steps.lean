module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Static
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.State

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace

open Silmaril.Languages.Starlark.Modules (globalSlot enter)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (InOrder)
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr resolveTracked)
open Silmaril.Languages.Starlark.Lists (State Address Capture Cell Outcome)

local notation "MResult" => Silmaril.Languages.Starlark.Modules.Result
local notation "Value" => Silmaril.Languages.Starlark.Lists.Value

theorem setup_value {globals : List String} {source : SourceExpr} (allowed : Initializer globals source)
    (state : State) : ∃ code reads out, resolveTracked ⟨[], globals⟩ source = .ok (code, reads) ∧
      Leaf.Setup globals state source code out ∧
      (∀ value next, out = .ok value next → next = state ∨ ∃ cell : Cell, next = { state with heap := state.heap.push cell }) := by
  cases allowed with
  | operand operand =>
    obtain ⟨code, related⟩ := operands_related operand
    obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
    obtain ⟨out, evaluated, same⟩ := RootCall.operand_total related state
    refine ⟨code, reads, out, tracked, .atom related evaluated, ?_⟩
    intro value next equal
    exact .inl (by rw [equal] at same; exact same)
  | @list items allowed =>
    obtain ⟨codes, related⟩ := actuals_related items allowed
    obtain ⟨reads, tracked, _⟩ := RootCall.resolves_display related
    rcases RootCall.operands_total related state with ⟨values, evaluated⟩ | ⟨error, evaluated⟩
    · refine ⟨_, reads, _, tracked, .list related evaluated, ?_⟩
      intro _ next equal
      change EStateM.Result.ok _ { state with heap := state.heap.push ⟨.list values, false⟩ } = _ at equal
      cases equal
      exact .inr ⟨_, rfl⟩
    · exact ⟨_, reads, _, tracked, .list related evaluated, fun _ _ equal => nomatch equal⟩
  | @tuple items allowed =>
    obtain ⟨codes, related⟩ := actuals_related items allowed
    obtain ⟨reads, _, tracked⟩ := RootCall.resolves_display related
    rcases RootCall.operands_total related state with ⟨values, evaluated⟩ | ⟨error, evaluated⟩
    · refine ⟨_, reads, _, tracked, .tuple related evaluated, ?_⟩
      intro _ next equal
      unfold Outcome.resume Silmaril.Languages.Starlark.Lists.allocateTuple at equal
      cases equal
      exact .inr ⟨_, rfl⟩
    · exact ⟨_, reads, _, tracked, .tuple related evaluated, fun _ _ equal => nomatch equal⟩

theorem setup_step {before rest : List Command} {globals : List String} {name : String} {source : SourceExpr}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign name source :: rest) globals)
    (checked : resolve (before ++ .assign name source :: rest) linked = .ok resolved)
    (allowed : Initializer globals source) (state : State) :
    ∃ out, Leaf.Step resolved globals before.length state (.assign name source) out ∧
      (∀ final, out = .ok () final → ∃ value next,
        final = next.write (globalSlot name) value ∧
        (next = state ∨ ∃ cell : Cell, next = { state with heap := state.heap.push cell })) := by
  obtain ⟨code, reads, out, tracked, evaluated, extension⟩ := setup_value allowed state
  have site := RootCall.checked_assign_site before rest name source code reads globals linked resolved
    declared checked tracked
  refine ⟨Leaf.assignResult name out, .setup site evaluated, ?_⟩
  intro final found
  cases out with
  | error error next => cases found
  | ok value next =>
    cases found
    exact ⟨value, next, rfl, extension _ _ rfl⟩

theorem call_step {before rest : List Command} {globals : List String} {name destination : String}
    {arguments : List SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation name destination arguments :: rest) globals)
    (checked : resolve (before ++ invocation name destination arguments :: rest) linked = .ok resolved)
    (callee : Visible globals name) (allowed : ∀ arg ∈ arguments, Operand globals arg)
    {state : State} {address id : Nat} {captures : List Capture} {frozen : Bool} {frame : Frame}
    (live : RootCall.Live state name address id captures frozen)
    (found : resolved.program[id]? = some frame.declaration)
    (continues : State → Prop)
    (body : ∀ assigned, ∃ out, Leaf.BodyRuns resolved.program state frame captures assigned out ∧
      (∀ value next, out = .ok value next → continues (next.write (globalSlot destination) value))) :
    ∃ out, Leaf.Step resolved globals before.length state (invocation name destination arguments) out ∧
      (∀ next, out = .ok () next → continues next) := by
  obtain ⟨actuals, related⟩ := actuals_related arguments allowed
  have calleeCode := global_operand callee
  have site := RootCall.checked_call_assignment_site before rest destination _ arguments _ actuals globals
    linked resolved declared checked calleeCode related
  rcases RootCall.operands_total related state with ⟨values, evaluated⟩ | ⟨error, failed⟩
  · obtain ⟨binding, binds⟩ := Entry.binds_total frame.parameters values
    cases binding with
    | error error =>
      exact ⟨.error (.runtime error) state,
        .call site calleeCode related evaluated live.binding live.cell found binds rfl,
        fun _ equal => nomatch equal⟩
    | ok assigned =>
      obtain ⟨out, ran, continues⟩ := body assigned
      refine ⟨Leaf.assignResult destination out,
        .call site calleeCode related evaluated live.binding live.cell found binds ran, ?_⟩
      intro next written
      cases out with
      | error error final => cases written
      | ok value final =>
        cases written
        exact continues value final rfl
  · have read : RootCall.Evaluates state (.scalar (.read name)) (.ok (.function address) state) := by
      simpa [State.read, live.binding] using RootCall.Evaluates.name (state := state) name
    have stopped : RootCall.EvaluatesOperands state (.scalar (.read name) :: arguments) (.error error state) :=
      .cons read failed
    exact ⟨.error (.runtime error) state, .operandError site calleeCode related stopped,
      fun _ equal => nomatch equal⟩

/-- The source wrapper derives its child captures. Their addresses and the
new closure cell survive caller restoration and the assignment at the call site. -/
theorem child_total {seed program : Program} {globals : List String} {outer : List (List String)}
    {name : String} {params : List String} {child : Chain} {frame childFrame : Frame} {rest : List Frame}
    (emits : Emits globals outer (.wrapper name params child) (frame :: childFrame :: rest))
    (links : Links seed (.wrapper name params child) (frame :: childFrame :: rest))
    (keeps : Wrapper.KeepsTable seed program (frame :: childFrame :: rest))
    (state : State) (layout : ModuleSlots globals state) {destination : String} (declared : destination ∈ globals)
    (captures : List Capture) (environment : ∃ owner, Installs owner frame.free captures)
    (captureLegal : ∀ entry ∈ captures, entry.binding.name.toList.head? ≠ some '$')
    (ownedLegal : ∀ name ∈ frame.owned, name.toList.head? ≠ some '$')
    (assigned : List (Silmaril.Languages.Starlark.Binding × Value)) :
    ∃ out, Leaf.BodyRuns program state frame captures assigned out ∧
      (∀ value next, out = .ok value next →
        let stored := next.write (globalSlot destination) value
        ModuleSlots globals stored ∧
        (next.slots = state.slots ∧ ∀ index, index < state.heap.size → next.heap[index]? = state.heap[index]?) ∧
        ∃ address selected, RootCall.Live stored destination address (EmittedProgram seed rest).size selected false ∧
          (∃ owner, Installs owner childFrame.free selected) ∧
          (∀ entry ∈ selected, entry.binding.name.toList.head? ≠ some '$')) := by
  obtain ⟨selected, returned⟩ := Wrapper.wrapper_total (seed := seed) emits state captures assigned environment
  let active := activate state frame.declaration captures assigned
  let id := (EmittedProgram seed rest).size
  let next := restoreCaller state (Wrapper.installChild active child.name id selected)
  have exactReturn : Wrapper.ReturnsChild seed state child frame childFrame rest captures assigned selected
      (.ok (.function active.heap.size) next) := returned
  refine ⟨_, .wrapper links keeps exactReturn, ?_⟩
  intro value final outcome
  cases outcome
  have ⟨slots, cells⟩ := Wrapper.returned_preserves exactReturn
  have restored := retains_slots layout slots cells
  obtain ⟨target, previous, frozen, owned, bindingCell⟩ := restored.usable destination declared
  have installed : Installs active childFrame.free selected := by cases exactReturn; assumption
  have closureCell : next.heap[active.heap.size]? = some ⟨.function ⟨id, selected, []⟩, false⟩ := by
    change (({ active with heap := active.heap.push ⟨.function ⟨id, selected, []⟩, false⟩ } : State).write
      (Silmaril.Languages.Starlark.Modules.fileSlot child.name) (.function active.heap.size)).heap[
        active.heap.size]? = _
    exact write_keeps_function _ _ _ _ _ _ (by simp)
  exact ⟨written_slots restored _ _, ⟨slots, cells⟩, active.heap.size, selected,
    ⟨⟨target, by rw [slots_write]; exact owned⟩, writes_binding _ _ _ _ owned bindingCell,
      write_keeps_function _ _ _ _ _ _ closureCell⟩,
    ⟨active, installed⟩,
    capture_names_from_slots installed (Leaf.activate_no_private state frame captures assigned ownedLegal captureLegal)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace
