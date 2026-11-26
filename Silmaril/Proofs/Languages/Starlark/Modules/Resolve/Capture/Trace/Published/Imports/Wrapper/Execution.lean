module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Link
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Modules.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
  (runs_at runs_at_reached)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Capture Cell Slot State Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

private theorem keeps_push (state : State) (cell : Cell) :
    Body.Keeps state.heap.size state {state with heap := state.heap.push cell} := by
  exact ⟨rfl, fun address _ below found => by simp [Array.getElem?_push, Nat.ne_of_lt below, found]⟩

private theorem reached_return (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) {callee : Callable}
    (known : callee.Linked producer) {installed defining : State} {origin aliasCell : Nat} {frozen : Bool}
    (record : ClosureAt callee.site callee.id defining installed origin)
    (aliasStored : installed.heap[aliasCell]? = some ⟨.binding (some (.function origin)), frozen⟩)
    (packed : State) (kept : Body.Keeps installed.heap.size installed packed) (assigned : List (Binding × Lists.Value)) :
    let capture : Capture := ⟨fileSlot wrapper.alias, aliasCell, true⟩
    let active := activate packed wrapper.site.declaration [capture] assigned
    ∃ out, wrapper.Returns callee active out ∧
      Exec consumer.program (withoutDeclaration (List.range consumer.program.size) producer.size)
        active wrapper.site.body.code out ∧
      Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)) := by
  intro capture active
  have ⟨extension, _, guarded⟩ := linked wrapper checked
  let available := withoutDeclaration (List.range consumer.program.size) producer.size
  have native := enter_callable_for checked known extension available guarded
  have extended := linked_extends known extension
  have present : callee.id ∈ available :=
    guarded (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp known.1).choose)
  have captures : active.slots (fileSlot wrapper.alias) = some (.captured aliasCell true) :=
    activate_capture packed wrapper.site.declaration [capture] capture assigned (by simp) (by change ¬ _ ∈ ([] : List Binding); simp)
  have stored := kept.2 _ _ (Array.getElem?_eq_some_iff.mp aliasStored).choose aliasStored
  have sameHeap (address : Nat) (cell : Cell) (found : packed.heap[address]? = some cell) :
      active.heap[address]? = some cell :=
    (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activation_preserves packed
      wrapper.site.declaration [capture] assigned address (Array.getElem?_eq_some_iff.mp found).choose).trans found
  have aliasRead : active.bindingValue (fileSlot wrapper.alias) = .ok (.function origin) := by
    simp [State.bindingValue, captures, Slot.address, sameHeap _ _ stored]
  have read := Body.Evaluates.read (state := active)
    (Assignment.ReadResolves.enclosing (block := wrapper.site.block) (name := wrapper.alias)
      (by change ¬ _ ∈ ([] : List String); simp) (by change _ ∈ [wrapper.alias]; simp))
  change Body.Evaluates _ _ _ _ (active.read (.bound (fileSlot wrapper.alias))) at read
  rw [State.read, aliasRead] at read
  obtain ⟨packedRecord⟩ := keep_record record kept
  let reached : ClosureAt callee.site callee.id defining active origin := {
    packedRecord with
    recorded := sameHeap _ _ packedRecord.recorded
    live := fun selected member => by
      obtain ⟨value, flag, found⟩ := packedRecord.live selected member
      exact ⟨value, flag, sameHeap _ _ found⟩ }
  obtain ⟨result, source, exec, _, preserved⟩ :=
    runs_at callee.site callee.BodyRuns checked callee.id extended.1 available present
      native (fileSlot wrapper.alias) read reached wrapper.operands wrapper.keywords wrapper.star wrapper.mapping
  have finished : finishState (result.resume (fun value => pure (Flow.returned value))) = finishState result := by
    cases result <;> rfl
  refine ⟨_, ⟨result, source, rfl⟩, .returnExpr exec, Body.returned_keeps packed wrapper.site.declaration
    [capture] assigned _ ?_⟩
  rw [finished]
  exact ⟨preserved.1, fun address cell _ found => preserved.2 address cell
    (Array.getElem?_eq_some_iff.mp found).choose found⟩

theorem run_bound (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) {callee : Callable}
    (known : callee.Linked producer) {state defining : State} {origin aliasCell targetCell : Nat}
    {frozen targetFrozen : Bool} {old : Option Lists.Value}
    (record : ClosureAt callee.site callee.id defining state origin)
    (aliasOwned : state.slots (fileSlot wrapper.alias) = some (.owned aliasCell))
    (aliasStored : state.heap[aliasCell]? = some ⟨.binding (some (.function origin)), frozen⟩)
    (targetOwned : state.slots (globalSlot wrapper.name) = some (.owned targetCell))
    (targetStored : state.heap[targetCell]? = some ⟨.binding old, targetFrozen⟩)
    (distinct : aliasCell ≠ targetCell) (manifest : Modules.Loader.Manifest) :
    ∃ out, wrapper.Runs producer.size callee state out ∧
      ∀ cache, Modules.Loader.Runs consumer.program manifest [1]
        (.commands 1 ((wrapper.moduleCode producer).drop 1)) ⟨state, cache⟩
        (Modules.Loader.liftResult 1 ⟨state, cache⟩ out) := by
  have ⟨_, found, _⟩ := linked wrapper checked
  let capture : Capture := ⟨fileSlot wrapper.alias, aliasCell, true⟩
  have installed : Installs state wrapper.site.free [capture] := .cons (.enclosing aliasOwned) .nil
  let cell : Cell := ⟨.function ⟨producer.size, [capture], []⟩, false⟩
  let grown : State := {state with heap := state.heap.push cell}
  let next := grown.write (globalSlot wrapper.name) (.function state.heap.size)
  have source : Lexical.DefinesFor wrapper.parent (globalSlot wrapper.name) producer.size wrapper.site.free [] []
      state (.ok .next next) := .installed .nil installed
  have defined := (Lexical.defines_agree consumer.program (List.range consumer.program.size) (globalSlot wrapper.name)
    producer.size wrapper.site.parameters wrapper.site.declaration .nil found rfl source).1
  have pushed := keeps_push state cell
  have targetGrown := pushed.2 _ _ (Array.getElem?_eq_some_iff.mp targetStored).choose targetStored
  have aliasGrown := pushed.2 _ _ (Array.getElem?_eq_some_iff.mp aliasStored).choose aliasStored
  have aliased : next.heap[aliasCell]? = some ⟨.binding (some (.function origin)), frozen⟩ :=
    (RootCall.write_other_cell grown _ _ aliasCell (by rw [show grown.slots = state.slots from rfl, targetOwned]; simpa using distinct.symm)).trans aliasGrown
  have ⟨grownRecord⟩ := keep_record record pushed
  have ⟨afterRecord⟩ := write_slot_record grownRecord targetOwned targetGrown (.function state.heap.size)
  let wrapperRecord : ClosureAt wrapper.site producer.size state next state.heap.size := {
    captures := [capture]
    defaults := []
    frozen := false
    length := rfl
    recorded := (RootCall.write_other_cell grown _ _ state.heap.size (by
      rw [show grown.slots = state.slots from rfl, targetOwned]
      simp [Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp targetStored).choose])).trans Array.getElem?_push_size
    installed := installed
    live := fun selected member => by
      simp only [List.mem_singleton] at member
      subst selected
      exact ⟨_, frozen, aliased⟩ }
  have loaded : next.bindingValue (globalSlot wrapper.name) = .ok (.function state.heap.size) := by
    simp [State.bindingValue, next, write_slots, Slot.address, show grown.slots = state.slots from rfl, targetOwned,
      written_cell (.function state.heap.size) (state := grown) targetOwned targetGrown]
  have read := Body.Evaluates.read (state := next)
    (Assignment.ReadResolves.global (block := wrapper.parent) (name := wrapper.name)
      (by simpa [Wrapper.parent, block] using wrapper.separate) (by simp [Wrapper.parent, block]) wrapper.site.target)
  change Body.Evaluates _ _ _ _ (next.read (.bound (globalSlot wrapper.name))) at read
  rw [State.read, loaded] at read
  have permitted : producer.size ∈ List.range consumer.program.size :=
    List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
  obtain ⟨result, called, ran, _, _⟩ := runs_at_reached wrapper.site (wrapper.Returns callee) checked
    producer.size found _ permitted (globalSlot wrapper.name) read wrapperRecord
    (fun packed kept assigned =>
      reached_return wrapper checked known (installed := next) afterRecord aliased packed kept assigned)
    .nil .empty none none
  refine ⟨afterWrite wrapper.destination result, .invoked source called, fun cache => ?_⟩
  have invoked : Exec consumer.program (List.range consumer.program.size) next
      (.assignExpr (globalSlot wrapper.destination) wrapper.invokeCode)
      (result.resume fun value => fun reached => .ok .next (reached.write (globalSlot wrapper.destination) value)) :=
    .assignExpr ran
  have callStep : Modules.Loader.Runs consumer.program manifest [1]
      (.command 1 (.exec (.assignExpr wrapper.destination wrapper.invokeCode))) ⟨next, cache⟩
      (Modules.Loader.liftResult 1 ⟨state, cache⟩ (afterWrite wrapper.destination result)) := by
    have step := Modules.Loader.Runs.exec (manifest := manifest) (active := [1]) (requester := 1)
      (code := .assignExpr wrapper.destination wrapper.invokeCode) (s := ⟨next, cache⟩) invoked
    cases result <;> exact step
  have tail : Modules.Loader.Runs consumer.program manifest [1]
      (.commands 1 [.exec (.assignExpr wrapper.destination wrapper.invokeCode)]) ⟨next, cache⟩
      (Modules.Loader.liftResult 1 ⟨state, cache⟩ (afterWrite wrapper.destination result)) := by
    cases result with
    | error => exact .failed callStep
    | ok => exact .step callStep .done
  have defStep : Modules.Loader.Runs consumer.program manifest [1]
      (.command 1 (.exec (.define wrapper.name producer.size))) ⟨state, cache⟩ (.ok () ⟨next, cache⟩) :=
    Modules.Loader.Runs.exec (code := .define wrapper.name producer.size) (s := ⟨state, cache⟩) defined
  exact .step defStep tail

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper
