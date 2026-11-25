module

import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms
import Silmaril.Languages.Python.Core.Closure.Executor.Thms
import Mathlib.Data.List.AList

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

open Closure.Executor (Continuation)

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev calleeLayout : Layout := ⟨2, 0, 1⟩
private def cell : CellId := ⟨0⟩
private def heap : HeapTable := HeapTable.empty.reserve 1
private def residual : HeapTable := heap.bind cell (.int 7) (by decide)
private def frame : Frame callerLayout := ⟨fun _ => some (.int 41), fun _ => cell, Fin.elim0⟩
private def observedCell : Slot callerLayout := .owned 0
private def next : Closure.Executor.Body callerLayout := .ret (.read observedCell)
private def caller : Call.Saved Continuation := ⟨callerLayout, frame, ⟨.discard, next⟩⟩
private def ref : CodeRef := ⟨17, calleeLayout⟩
private def selected : Fin calleeLayout.captures → CaptureSlot callerLayout := fun _ => .owned 0
private def callee : Value := .function (frame.closure ref selected)

private def code (body : Closure.Executor.Body calleeLayout) : CodeRows :=
  (∅ : CodeRows).insert ref.key
    ⟨calleeLayout, ⟨⟨[.local 0], by decide⟩, .store (.capture 0) (.read (.local 0)) body⟩⟩

private def start : State :=
  .running ⟨heap, frame⟩ (.callTo .discard (.closure ref selected) [.literal (.int 7)] next) []

private def returning : CodeRows := code (.ret (.literal (.int 5)))
private def resumed : State := .running ⟨residual, frame⟩ next []
private def success : Result := .ok (.int 7)

-- The callee returns 5 after writing 7 to the shared cell. Discard leaves
-- both the restored frame and the residual heap intact. The tail reads 7.
example : runPrefix returning 5 start =
    ([.enter callee, .resume (.ok (.int 5))], resumed) := rfl

example : runPrefix returning 7 start =
    ([.enter callee, .resume (.ok (.int 5)), .complete success], .finished residual success) := rfl

private def receiving : State := .receiving residual caller [] (.ok (.int 5))
private def delivering : Closure.Executor.State := .delivering residual.project [] success
private def finished : Closure.Executor.State := .finished residual.project success

private theorem discardRun :
    (semantic returning.project).Execution receiving.project [none, none, some (.complete success)] finished
      [receiving.project, resumed.project, delivering, finished] :=
  .stepL (.receiveDiscard rfl)
    (.stepL (.ret (.read observedCell)) (.stepL (.complete _ _) (.refl _)))

example : ∃ final states, (presented returning).Execution receiving [none, none, some (.complete success)]
      final states ∧ states.map State.project = [receiving.project, resumed.project, delivering, finished] ∧
    final.project = finished :=
  execution_readback discardRun

private def failing : CodeRows := code (.ret (.read (.local 1)))
private def failure : Result := .error (.unboundLocal 1)

example : runPrefix failing 6 start =
    ([.enter callee, .resume failure, .complete failure], .finished residual failure) := rfl

private def missing : CodeRef := ⟨99, ⟨0, 0, 0⟩⟩
private def faulting : CodeRows := code (.callTo .discard (.closure missing Fin.elim0) [] (.ret (.literal .none)))

example : runPrefix faulting 7 start =
    ([.enter callee, .fault (.missingCode 99)], .faulted residual [caller] (.missingCode 99)) := rfl

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
