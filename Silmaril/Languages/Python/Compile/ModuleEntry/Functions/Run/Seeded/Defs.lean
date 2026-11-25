module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs

/-! # Run checked module-call instructions with an explicit closed seed -/

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Source (Scope)
open Core.Module.SeededCall (AssertionArgument Bindings CallObservation Failure Namespace Value)

inductive SeedPlacement where
  | builtin
  | preamble

/-- Only this explicit profile supplies harness entries. In either placement,
the class token is a builtin and the helpers use the chosen namespace. -/
def legacySeed (placement : SeedPlacement) : Namespace :=
  let classes : Bindings := [("AssertionError", .exceptionClass .assertionError)]
  let helpers (diagnostic : AssertionArgument) : Bindings :=
    [("___assertEqual", .helper .assertEqual), ("___assertRaises", .helper (.assertRaises diagnostic))]
  match placement with
  | .builtin => ⟨[], classes ++ helpers .empty⟩
  | .preamble => ⟨helpers (.text "did not raise exception"), classes⟩

def lowerCallOperand : Core.Module.Functions.Operand → Core.Module.SeededCall.Operand 0
  | .readGlobal name => .global name
  | .literal (.int value) => .literal (.int value)
  | .literal _ => .unsupported

def lowerScalarOperand {scope : Scope} : ModuleEntry.Operand scope → Core.Module.SeededCall.Operand 0
  | .read name _ => .global name
  | .integer value => .literal (.int value)
  | .boolean _ | .binary .. => .unsupported

def assertTruth : Value → Except Failure Unit
  | .int 0 | .none => .error (.raised (.assertionError .empty))
  | _ => .ok ()

def acceptCall (destination : Core.Module.Functions.Destination) (value : Value) :
    Except Failure (Option (String × Value)) :=
  match destination with
  | .discard => .ok none
  | .bindGlobal name => .ok (some (name, value))
  | .assert => (assertTruth value).map fun _ => none

structure CallEvent where
  callee : String
  observation : CallObservation

structure Effect where
  binding : Except Failure (Option (String × Value))
  call : Option CallEvent := none

def effect {scope : Scope} (space : Namespace) : Instruction scope → Effect
  | .scalar (.assign name _ operand) =>
    ⟨((lowerScalarOperand operand).eval space #v[]).map fun value => some (name, value), none⟩
  | .scalar (.assertion operand) =>
    ⟨(((lowerScalarOperand operand).eval space #v[]).bind assertTruth).map fun _ => none, none⟩
  | .publish .. => ⟨.error .unsupported, none⟩
  | .call destination name arguments =>
    let observed := Core.Module.SeededCall.runObserved space #v[] (.global name) (arguments.map lowerCallOperand)
    ⟨observed.result.bind (acceptCall destination), some ⟨name, observed⟩⟩

structure Observation where
  residual : Namespace
  completion : Except Failure Unit
  calls : List CallEvent

/-- Execute the checked stream in source order. A failed instruction keeps
its incoming namespace and stops the stream. -/
def runInstructions {scope : Scope} (space : Namespace) : List (Instruction scope) → Observation
  | [] => ⟨space, .ok (), []⟩
  | instruction :: rest =>
    let item := effect space instruction
    match item.binding with
    | .error error => ⟨space, .error error, item.call.toList⟩
    | .ok binding =>
      let updated := binding.elim space fun (name, value) => space.bindGlobal name value
      let tail := runInstructions updated rest
      { tail with calls := item.call.toList ++ tail.calls }

/-- Seeded execution starts from the same compiled instruction stream as
ordinary module execution. The caller supplies the namespace explicitly. -/
def run {source : Source.Module} (space : Namespace) (compiled : Compiled source) : Observation :=
  runInstructions space compiled.instructions

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
