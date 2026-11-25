module

import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

open Silmaril.Languages.Python
open Core.Closure (Heap Layout)
open Core.Closure.Executor (CodeTable)
open Core.Module.Functions (TopFunction)
open Core.Module.SeededCall (Namespace)
open Compile.ModuleEntry.Functions.Run (Instruction)
open Compile.ModuleEntry.Functions.Run.Seeded (runInstructions)

private def top : TopFunction :=
  ⟨⟨11, ⟨0, 0, 0⟩⟩, rfl⟩

private def table : CodeTable :=
  fun key => if key = 11 then
    some ⟨top.ref.layout, { parameters := ⟨[], by decide⟩, body := .ret (.literal .none) }⟩
  else none

private def initial : Namespace :=
  ⟨[("kept", .int 5)], [("f", .helper .assertEqual), ("AssertionError", .exceptionClass .assertionError)]⟩

private def heap : Heap := ⟨1, fun address => if address = 0 then some (.int 17) else none⟩

private def instructions (scope : Source.Scope) : List (Instruction scope) := [.publish "f" top]

example (scope : Source.Scope) :
    runInstructions initial (instructions scope) table heap =
      ⟨⟨[("f", .function top.closure), ("kept", .int 5)], initial.builtins⟩, .ok (), [], heap⟩ := rfl

example (scope : Source.Scope) :
    (runInstructions initial (instructions scope) table heap).residual.lookupGlobal "f" =
      some (.function top.closure) := rfl

example (scope : Source.Scope) :
    runInstructions initial (instructions scope) (fun _ => none) heap =
      ⟨initial, .error (.publicationFault (.missingCode 11)), [], heap⟩ := rfl

private def wrong : TopFunction := ⟨⟨11, ⟨1, 0, 0⟩⟩, rfl⟩

example (scope : Source.Scope) :
    runInstructions initial ([.publish "f" wrong, .publish "after" top] : List (Instruction scope)) table heap =
      ⟨initial, .error (.publicationFault (.layoutMismatch wrong.ref.layout top.ref.layout)), [], heap⟩ := rfl

example (scope : Source.Scope) :
    (runInstructions initial
      ([.publish "f" top, .call .discard "f" [.readGlobal "missing"]] : List (Instruction scope))
      table heap).completion =
        .error (.raised (.runtime (.nameError "missing"))) := rfl

#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_publication
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_publication_fault
#print axioms Compile.ModuleEntry.Functions.Run.Seeded.run_preserves_heap
