module

import Silmaril.Languages.Python.Core.Closure.Executor.Thms

open Silmaril.Languages.Python.Core.Closure
open Silmaril.Languages.Python.Core.Closure.Executor

private def callerLayout : Layout := ⟨2, 1, 0⟩
private def output : Slot callerLayout := .local ⟨0, by decide⟩
private def initial : Heap × Frame callerLayout := Frame.fresh Heap.empty Fin.elim0
private def caller : Frame callerLayout :=
  { initial.2 with locals := fun slot => if slot.val = 1 then some (.int 19) else none }
private def cell : CellId := caller.owned ⟨0, by decide⟩
private def next : Body callerLayout := .ret (.read output)
private def saved : Call.Saved Continuation := ⟨callerLayout, caller, ⟨output, next⟩⟩

private def olderLayout : Layout := ⟨1, 0, 0⟩
private def olderOutput : Slot olderLayout := .local ⟨0, by decide⟩
private def older : Call.Saved Continuation :=
  ⟨olderLayout, (Frame.fresh Heap.empty Fin.elim0).2, ⟨olderOutput, .ret (.read olderOutput)⟩⟩

private def calleeCode : CodeRef := ⟨17, ⟨2, 0, 1⟩⟩
private def parameter : Fin calleeCode.layout.locals := ⟨0, by decide⟩
private def unset : Slot calleeCode.layout := .local ⟨1, by decide⟩
private def capture : Slot calleeCode.layout := .capture ⟨0, by decide⟩
private def tableWith (body : Body calleeCode.layout) : CodeTable :=
  fun key => if key = calleeCode.key then
    some ⟨calleeCode.layout, ⟨⟨[.local parameter], by decide⟩,
      .store capture (.read (.local parameter)) body⟩⟩
  else none

private def table (operand : Operand calleeCode.layout) : CodeTable :=
  tableWith (.ret operand)

private def start : State :=
  .running initial.1 caller
    (.call output (.closure calleeCode (fun _ => .owned ⟨0, by decide⟩)) [.literal (.int 7)] next) [older]

private def resumed (body : Body calleeCode.layout) (result : Result) : Prop :=
  let (log, state) := runPrefix (tableWith body) 4 start
  match log, state with
  | [.enter _, .resume delivered], .receiving residual restored parents observed =>
    restored = saved ∧ parents = [older] ∧ delivered = result ∧ observed = result ∧
      residual.lookup cell = some (some (.int 7))
  | _, _ => False

-- Both cases read back the exact saved frame and the older stack. The callee's
-- capture write persists even when its subsequent return operand raises.
example : resumed (.ret (.read capture)) (.ok (.int 7)) := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : resumed (.ret (.read unset)) (.error (.unboundLocal 1)) := ⟨rfl, rfl, rfl, rfl, rfl⟩

private def finished (body : Body calleeCode.layout) (result : Result) : Prop :=
  let (log, state) := runPrefix (tableWith body) 12 start
  match log, state with
  | [.enter _, .resume first, .resume second, .complete delivered], .finished residual observed =>
    first = result ∧ second = result ∧ delivered = result ∧ observed = result ∧
      residual.lookup cell = some (some (.int 7))
  | _, _ => False

example : finished (.ret (.read capture)) (.ok (.int 7)) := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : finished (.ret (.read unset)) (.error (.unboundLocal 1)) := ⟨rfl, rfl, rfl, rfl, rfl⟩

private def falseAssertion : Body calleeCode.layout :=
  .assert (.literal (.bool false)) (.store capture (.literal (.int 99)) (.ret (.read capture)))

-- The earlier shared write survives delivery to both saved callers.
-- The write following the failed assertion is skipped.
example : resumed falseAssertion (.error .assertionError) := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : finished falseAssertion (.error .assertionError) := ⟨rfl, rfl, rfl, rfl, rfl⟩
example : finished (.assert (.read capture) (.ret (.read capture))) (.ok (.int 7)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
example : resumed (.assert (.read unset) (.ret (.read capture))) (.error (.unboundLocal 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def assertionAdvance (test : Operand callerLayout) : Option Transition :=
  advance (table (.read capture)) (.running initial.1 caller (.assert test next) [older])

private def assertionContinues (test : Operand callerLayout) : Prop :=
  assertionAdvance test = some (none, .running initial.1 caller next [older])

private def assertionRaises (test : Operand callerLayout) : Prop :=
  assertionAdvance test = some (none, .delivering initial.1 [older] (.error .assertionError))

example : assertionContinues (.literal (.bool true)) := rfl
example : assertionContinues (.literal (.int (-2))) := rfl
example : assertionContinues (.closure calleeCode (fun _ => .owned ⟨0, by decide⟩)) := rfl
example : assertionRaises (.literal (.int 0)) := rfl
example : assertionRaises (.literal .none) := rfl

example :
    assertionAdvance (.readGlobal "missing") =
      some (none, .delivering initial.1 [older] (.error (.nameError "missing"))) := rfl

example :
    advance (table (.read capture))
      (.running Heap.empty caller (.assert (.read (.owned ⟨0, by decide⟩)) next) [older]) =
      some (some (.fault (.danglingCell cell)), .faulted Heap.empty [older] (.danglingCell cell)) := rfl

example : assertionContinues (.eqInt (.slot (.local ⟨1, by decide⟩)) 19) := rfl
example : assertionRaises (.eqInt (.slot (.local ⟨1, by decide⟩)) 20) := rfl
example : finished (.assert (.eqInt (.slot capture) 7) (.ret (.read capture))) (.ok (.int 7)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
example : resumed (.assert (.eqInt (.slot unset) 0) (.ret (.read capture))) (.error (.unboundLocal 1)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private def compareGlobal (value : Value) (right : Int) : Option Transition :=
  let globals : GlobalLookup := fun name => if name = "operand" then some value else none
  advanceIn (table (.read capture)) globals
    (.running initial.1 caller (.assert (.eqInt (.global "operand") right) next) [older])

private def globalComparisonHolds (value : Value) (right : Int) : Prop :=
  compareGlobal value right = some (none, .running initial.1 caller next [older])

private def globalComparisonFails (value : Value) (right : Int) : Prop :=
  compareGlobal value right = some (none, .delivering initial.1 [older] (.error .assertionError))

example : globalComparisonHolds (.bool false) 0 := rfl
example : globalComparisonHolds (.bool true) 1 := rfl
example : globalComparisonFails (.bool true) 0 := rfl
example : globalComparisonFails .none 0 := rfl
example : globalComparisonFails (.function (caller.closure calleeCode (fun _ => .owned ⟨0, by decide⟩))) 0 := rfl

example :
    assertionAdvance (.eqInt (.global "missing") 0) =
      some (none, .delivering initial.1 [older] (.error (.nameError "missing"))) := rfl

example :
    advance (table (.read capture))
      (.running Heap.empty caller (.assert (.eqInt (.slot (.owned ⟨0, by decide⟩)) 0) next) [older]) =
      some (some (.fault (.danglingCell cell)), .faulted Heap.empty [older] (.danglingCell cell)) := rfl

-- Python evaluates arguments before reporting that an evaluated integer is
-- not callable. The first argument's failure also precedes the later read.
example :
    advance (table (.read capture))
      (.running initial.1 caller
        (.call output (.literal (.int 0)) [.read output, .read (.owned ⟨0, by decide⟩)] next) []) =
      some (none, .delivering initial.1 [] (.error (.unboundLocal 0))) := rfl

private def missing : CodeRef := ⟨18, ⟨0, 0, 0⟩⟩
example :
    advance (table (.read capture))
      (.running initial.1 caller (.call output (.closure missing Fin.elim0) [] next) [older]) =
      some (some (.fault (.missingCode 18)), .faulted initial.1 [older] (.missingCode 18)) := rfl

#print axioms step_iff
#print axioms step_deterministic
#print axioms run_path
#print axioms delivers_saved
