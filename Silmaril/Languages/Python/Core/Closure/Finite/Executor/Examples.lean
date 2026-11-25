module

import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Thms
import Silmaril.Languages.Python.Core.Closure.Executor.Thms
meta import Silmaril.Languages.Python.Core.Closure.Finite.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Finite.Defs
meta import Silmaril.Languages.Python.Core.Closure.Executor.Defs
meta import Silmaril.Languages.Python.Core.Closure.Dispatch.Defs
meta import Silmaril.Languages.Python.Core.Closure.Call.Defs
meta import Silmaril.Languages.Python.Core.Closure.Defs
meta import Mathlib.Data.List.AList

namespace Silmaril.Languages.Python.Core.Closure.Finite.Executor

private abbrev callerLayout : Layout := ⟨1, 1, 0⟩
private abbrev calleeLayout : Layout := ⟨2, 0, 1⟩
private def output : Slot callerLayout := .local 0
private def rest : Closure.Executor.Body callerLayout := .ret (.read output)
private def heap : HeapTable := HeapTable.empty.reserve 1
private def frame : Frame callerLayout :=
  ⟨fun _ => none, fun _ => ⟨0⟩, Fin.elim0⟩
private def caller : Call.Saved Closure.Executor.Continuation :=
  ⟨callerLayout, frame, ⟨output, rest⟩⟩
private abbrev olderLayout : Layout := ⟨1, 0, 0⟩
private def older : Call.Saved Closure.Executor.Continuation :=
  ⟨olderLayout, ⟨fun _ => none, Fin.elim0, Fin.elim0⟩, ⟨.local 0, .ret (.read (.local 0))⟩⟩
private def ref : CodeRef := ⟨17, calleeLayout⟩

private def code (result : Closure.Executor.Operand calleeLayout) : CodeRows :=
  (∅ : CodeRows).insert ref.key
    ⟨calleeLayout, ⟨⟨[.local 0], by decide⟩, .store (.capture 0) (.read (.local 0)) (.ret result)⟩⟩

private def start : State :=
  .running ⟨heap, frame⟩ (.call output (.closure ref (fun _ => .owned 0)) [.literal (.int 7)] rest) [older]

#guard
  match runPrefix (code (.read (.capture 0))) 12 start with
  | ([.enter _, .resume (.ok (.int 7)), .resume (.ok (.int 7)), .complete (.ok (.int 7))],
      .finished residual (.ok (.int 7))) =>
      match residual.rows.lookup 0 with
      | some (.int 7) => true
      | _ => false
  | _ => false

#guard
  match runPrefix (code (.read (.local 1))) 12 start with
  | ([.enter _, .resume (.error (.unboundLocal 1)), .resume (.error (.unboundLocal 1)),
        .complete (.error (.unboundLocal 1))], .finished residual (.error (.unboundLocal 1))) =>
      match residual.rows.lookup 0 with
      | some (.int 7) => true
      | _ => false
  | _ => false

example : advance (∅ : CodeRows) start =
    some (some (.fault (.missingCode 17)), .faulted heap [older] (.missingCode 17)) := rfl

private def residual : HeapTable := heap.bind ⟨0⟩ (.int 7) (by decide)
private def result : Result := .error (.unboundLocal 1)
private def table : CodeRows := code (.read (.local 1))
private def deliver : State := .delivering residual [caller, older] result
private def receive : Closure.Executor.State := .receiving residual.project caller [older] result
private def propagate : Closure.Executor.State := .delivering residual.project [older] result

private theorem deliveryRun :
    (semantic table.project).Execution deliver.project [some (.resume result), none]
      propagate [deliver.project, receive, propagate] :=
  .stepL (Closure.Executor.Step.resume _ caller [older] result)
    (.stepL (Closure.Executor.Step.receiveError _ caller [older] (.unboundLocal 1)) (.refl _))

example : ∃ final states,
    (presented table).Execution deliver [some (.resume result), none] final states ∧
      states.map State.project = [deliver.project, receive, propagate] ∧ final.project = propagate :=
  execution_readback deliveryRun

end Silmaril.Languages.Python.Core.Closure.Finite.Executor
