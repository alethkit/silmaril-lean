module

import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

open Silmaril.Languages.Python
open Core.Closure (CodeRef Heap Parameters)
open Core.Closure.Executor (Body CodeTable)
open Core.Module.Functions (TopFunction)
open Core.Module.SeededCall (Namespace)
open Compile.ModuleEntry.Functions.Run (Instruction)
open Compile.ModuleEntry.Functions.Run.Seeded

private abbrev top : TopFunction := ⟨⟨11, ⟨1, 1, 0⟩⟩, rfl⟩

private def table (tail : Body top.ref.layout) (parameters : Parameters top.ref.layout := ⟨[], by decide⟩) :
    CodeTable :=
  fun key => if key = 11 then
    some ⟨top.ref.layout,
      { parameters := parameters
        body := .store (.owned 0) (.literal (.int 7)) tail }⟩
  else none

private def initial : Namespace :=
  ⟨[], [("expect", .helper (.assertRaises .empty)), ("AssertionError", .exceptionClass .assertionError)]⟩

private def inputHeap : Heap := ⟨1, fun address => if address = 0 then some (.int 17) else none⟩
private def writeFresh (heap : Heap) : Heap :=
  ⟨heap.next + 1, fun address =>
    if address = heap.next then some (.int 7) else (heap.reserve 1).contents address⟩

private def residualHeap : Heap := writeFresh inputHeap

private def invoke {scope : Source.Scope} : Instruction scope :=
  .call (.bindGlobal "result") "expect" [.readGlobal "AssertionError", .readGlobal "f"]

private def published (space : Namespace) : Namespace := space.bindGlobal "f" (.function top.closure)

private def runCase (scope : Source.Scope) (tail : Body top.ref.layout) (fuel : Nat := 1000) : Observation :=
  runInstructions initial ([.publish "f" top, invoke] : List (Instruction scope)) (table tail) inputHeap fuel

example (scope : Source.Scope) :
    runCase scope (.assert (.literal (.int 0)) (.ret (.literal .none))) =
      ⟨(published initial).bindGlobal "result" .none, .ok (),
        [⟨"expect", ⟨.ok .none, some (.assertionError .empty)⟩⟩], residualHeap⟩ := by
  rfl

private def missingCode : CodeRef := ⟨99, ⟨0, 0, 0⟩⟩
private def faulting : Body top.ref.layout :=
  .call (.local 0) (.closure missingCode Fin.elim0) [] (.ret (.literal .none))

-- The catch boundary cannot turn a code fault into an AssertionError.
example (scope : Source.Scope) :
    runInstructions initial ([.publish "f" top, invoke, .publish "after" top] : List (Instruction scope))
        (table faulting) inputHeap =
      ⟨published initial, .error (.callbackFault (.missingCode 99)), [], residualHeap⟩ := by
  rfl

example (scope : Source.Scope) :
    runCase scope (.ret (.literal .none)) 2 =
      ⟨published initial, .error .callbackFuelExhausted, [], residualHeap⟩ := by
  rfl

example (scope : Source.Scope) :
    runCase scope (.ret (.literal (.int 42))) =
      ⟨published initial, .error (.raised (.assertionError .empty)),
        [⟨"expect", ⟨.error (.raised (.assertionError .empty)), none⟩⟩], residualHeap⟩ := rfl

private def nameErrorSeed : Namespace :=
  initial.bindGlobal "AssertionError" (.exceptionClass .nameError)

-- A helper resolved by the seeded namespace cannot masquerade as a catchable missing name.
example (scope : Source.Scope) :
    runInstructions nameErrorSeed ([.publish "f" top, invoke] : List (Instruction scope))
        (table (.ret (.readGlobal "expect"))) inputHeap =
      ⟨published nameErrorSeed, .error .unsupported,
        [⟨"expect", ⟨.error .unsupported, none⟩⟩], residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runInstructions (published initial) ([invoke] : List (Instruction scope))
        (table (.ret (.literal .none))) inputHeap =
      ⟨published initial, .error .unsupported, [⟨"expect", ⟨.error .unsupported, none⟩⟩], inputHeap⟩ := by
  rfl

private def twice (scope : Source.Scope) : Observation :=
  runInstructions initial ([.publish "f" top, invoke, invoke] : List (Instruction scope))
    (table (.assert (.literal (.int 0)) (.ret (.literal .none)))) inputHeap

example (scope : Source.Scope) :
    (twice scope).heap = writeFresh residualHeap := rfl

private def directSeed : Namespace :=
  ⟨[("kept", .int 5)], [("f", .helper .assertEqual), ("kept", .int 8), ("masked", .int 1)]⟩

private def discardCall {scope : Source.Scope} : Instruction scope := .call .discard "f" []

private def runDirect (scope : Source.Scope) (body : Body top.ref.layout)
    (rest : List (Instruction scope) := []) (fuel : Nat := 1000) : Observation :=
  runInstructions directSeed (.publish "f" top :: discardCall :: rest) (table body) inputHeap fuel

private def returnsNone : Body top.ref.layout := .ret (.literal .none)

-- Module bindings shadow the builtin callee and the builtin value read by its body.
example (scope : Source.Scope) :
    runDirect scope (.ret (.readGlobal "kept")) =
      ⟨published directSeed, .ok (), [⟨"f", ⟨.ok (.int 5), none⟩⟩], residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runDirect scope returnsNone [discardCall] =
      ⟨published directSeed, .ok (),
        [⟨"f", ⟨.ok .none, none⟩⟩, ⟨"f", ⟨.ok .none, none⟩⟩], writeFresh residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runDirect scope (.assert (.literal (.bool false)) returnsNone) [.publish "after" top] =
      ⟨published directSeed, .error (.raised (.assertionError .empty)),
        [⟨"f", ⟨.error (.raised (.assertionError .empty)), none⟩⟩], residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runDirect scope (.ret (.readGlobal "absent")) [.publish "after" top] =
      ⟨published directSeed, .error (.raised (.runtime (.nameError "absent"))),
        [⟨"f", ⟨.error (.raised (.runtime (.nameError "absent"))), none⟩⟩], residualHeap⟩ := rfl

private def maskedSeed : Namespace := directSeed.bindGlobal "masked" (.helper .assertEqual)

example (scope : Source.Scope) :
    runInstructions maskedSeed ([.publish "f" top, discardCall, .publish "after" top] : List (Instruction scope))
        (table (.ret (.readGlobal "masked"))) inputHeap =
      ⟨published maskedSeed, .error .unsupported, [⟨"f", ⟨.error .unsupported, none⟩⟩], residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runDirect scope faulting [.publish "after" top] =
      ⟨published directSeed, .error (.directCallFault (.missingCode 99)), [], residualHeap⟩ := rfl

private def staleCode : CodeRef := ⟨top.ref.key, ⟨0, 0, 0⟩⟩

example (scope : Source.Scope) :
    runDirect scope (.callTo .discard (.closure staleCode Fin.elim0) [] returnsNone) [.publish "after" top] =
      ⟨published directSeed, .error (.directCallFault (.layoutMismatch staleCode.layout top.ref.layout)), [],
        residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runDirect scope returnsNone [.publish "after" top] 2 =
      ⟨published directSeed, .error .directCallFuelExhausted, [], residualHeap⟩ := rfl

example (scope : Source.Scope) :
    runInstructions (published directSeed) ([discardCall] : List (Instruction scope)) (table returnsNone) inputHeap =
      ⟨published directSeed, .error .unsupported, [⟨"f", ⟨.error .unsupported, none⟩⟩], inputHeap⟩ := rfl

example (scope : Source.Scope) :
    runInstructions directSeed ([.publish "f" top, discardCall] : List (Instruction scope))
        (table returnsNone ⟨[.local 0], by decide⟩) inputHeap =
      ⟨published directSeed, .error .unsupported, [⟨"f", ⟨.error .unsupported, none⟩⟩], inputHeap⟩ := rfl

#print axioms callback_path
#print axioms callback_delivers
#print axioms invokeCall_published
#print axioms callback_fault
#print axioms run_directDiscard
#print axioms run_directDiscard_unsupported
