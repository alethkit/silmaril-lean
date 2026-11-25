module

import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms
import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Mathlib.Data.List.AList

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

private abbrev callerLayout : Layout := ⟨2, 0, 0⟩
private abbrev capturedLayout : Layout := ⟨0, 0, 2⟩
private abbrev closedLayout : Layout := ⟨0, 0, 0⟩

private def aliasSlot : Slot callerLayout := .local 1
private def capturedRef : CodeRef := ⟨17, capturedLayout⟩
private def closedRef : CodeRef := ⟨18, closedLayout⟩
private def captured : Function := Function.ofCaptureList capturedRef [⟨1⟩, ⟨0⟩] rfl
private def closed : Function := Function.ofCaptureList closedRef [] rfl

private def heap : HeapTable :=
  let allocated := HeapTable.empty.reserve 2
  let first := allocated.bind ⟨0⟩ (.int 11) (by decide)
  first.bind ⟨1⟩ (.int 13) (by decide)

private def environment (binding : Option Value) : Snapshot callerLayout :=
  ⟨heap, ⟨fun _ => binding, Fin.elim0, Fin.elim0⟩⟩

private def returnAlias : Closure.Executor.Body callerLayout := .ret (.read aliasSlot)

private def rows (closedMetadata : Option (List String)) : CodeRows :=
  let capturedEntry : Closure.Dispatch.Entry Closure.Executor.Body :=
    ⟨capturedLayout, {
      parameters := ⟨[], by decide⟩
      body := .ret (.read (.capture 0))
      freevars := some ["alpha", "zeta"] }⟩
  let closedEntry : Closure.Dispatch.Entry Closure.Executor.Body :=
    ⟨closedLayout, {
      parameters := ⟨[], by decide⟩
      body := .ret (.literal .none)
      freevars := closedMetadata }⟩
  ((∅ : CodeRows).insert capturedRef.key capturedEntry).insert closedRef.key closedEntry

private def profiled : CodeRows := rows (some [])

private def freevars (name : String) (expected : Bool) : Closure.Executor.FreevarsTest callerLayout :=
  ⟨.slot aliasSlot, name.toList.map Char.val, expected⟩

private def present : Closure.Executor.FreevarsTest callerLayout := freevars "alpha" true
private def absent : Closure.Executor.FreevarsTest callerLayout := freevars "omega" false
private def capturedEnvironment : Snapshot callerLayout := environment (some (.function captured))
private def start : State := .running capturedEnvironment (.assertFreevars present (.assertFreevars absent returnAlias)) []
private def afterIn : State := .running capturedEnvironment (.assertFreevars absent returnAlias) []
private def afterNotIn : State := .running capturedEnvironment returnAlias []
private def success : Result := .ok (.function captured)
private def delivering : Closure.Executor.State := .delivering heap.project [] success
private def finished : Closure.Executor.State := .finished heap.project success

-- Both assertions retain the exact frame, including the two aliases, and
-- the whole heap. Returning the alias retains its original capture order.
private theorem metadataRun :
    (semantic profiled.project).Execution start.project [none, none, none, some (.complete success)] finished
      [start.project, afterIn.project, afterNotIn.project, delivering, finished] :=
  .stepL (.assertFreevarsTrue rfl) (.stepL (.assertFreevarsTrue rfl)
    (.stepL (.ret (.read aliasSlot)) (.stepL (.complete _ _) (.refl _))))

example : ∃ last states, (presented profiled).Execution start [none, none, none, some (.complete success)] last states ∧
    states.map State.project = [start.project, afterIn.project, afterNotIn.project, delivering, finished] ∧
    last.project = finished :=
  execution_readback metadataRun

example : runPrefix profiled 4 start = ([.complete success], .finished heap success) := rfl

private def checking (binding : Option Value) (test : Closure.Executor.FreevarsTest callerLayout) : State :=
  .running (environment binding) (.assertFreevars test returnAlias) []

example : advance profiled (checking (some (.function closed)) (freevars "alpha" false)) =
    some (none, .running (environment (some (.function closed))) returnAlias []) := rfl

example : advance (rows none) (checking (some (.function closed)) (freevars "alpha" false)) =
    some (some (.fault (.unprofiledFreevars closedRef)), .faulted heap [] (.unprofiledFreevars closedRef)) := rfl

example : advance profiled (checking (some (.function closed)) present) =
    some (none, .delivering heap [] (.error .assertionError)) := rfl

example : advance profiled (checking none present) =
    some (none, .delivering heap [] (.error (.unboundLocal 1))) := rfl

example : advance profiled (checking (some (.int 7)) present) =
    some (some (.fault .unsupportedFreevarsReceiver), .faulted heap [] .unsupportedFreevarsReceiver) := rfl

example : advance (∅ : CodeRows) start =
    some (some (.fault (.missingCode 17)), .faulted heap [] (.missingCode 17)) := rfl

private def stale : Function := Function.ofCaptureList ⟨capturedRef.key, closedLayout⟩ [] rfl

example : advance profiled (checking (some (.function stale)) present) =
    some (some (.fault (.layoutMismatch closedLayout capturedLayout)),
      .faulted heap [] (.layoutMismatch closedLayout capturedLayout)) := rfl

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
