module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs

/-! # Run checked module-call instructions with an explicit closed seed -/

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Source (Scope)
open Core.Module.SeededCall (AssertionArgument Bindings CallObservation Failure Namespace Result Value)

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

def truth : Value → Bool
  | .int value => decide (value ≠ 0)
  | .none => false
  | .exceptionClass _ | .helper _ => true

def assertTruthAs (expected : Bool) (value : Value) : Except Failure Unit :=
  if truth value = expected then .ok () else .error (.raised (.assertionError .empty))

def assertTruth : Value → Except Failure Unit := assertTruthAs true

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
  calls : List CallEvent

def observeNamedCall (space : Namespace) (name : String)
    (arguments : List Core.Module.Functions.Operand) : CallEvent :=
  ⟨name, Core.Module.SeededCall.runObserved space #v[] (.global name) (arguments.map lowerCallOperand)⟩

def observeArgument (space : Namespace) : Argument → Result × List CallEvent
  | .scalar operand => ((lowerCallOperand operand).eval space #v[], [])
  | .call name arguments =>
    let event := observeNamedCall space name arguments
    (event.observation.result, [event])

def observeArguments (space : Namespace) :
    List Argument → Except Failure (List Value) × List CallEvent
  | [] => (.ok [], [])
  | argument :: rest =>
    let (result, calls) := observeArgument space argument
    match result with
    | .error error => (.error error, calls)
    | .ok value =>
      let (values, later) := observeArguments space rest
      (values.map (value :: ·), calls ++ later)

/-- A nested call resolves the outer name before visiting its arguments.
Only after those arguments return does it invoke the saved value. -/
def observeNestedCall (space : Namespace) (destination : Core.Module.Functions.Destination)
    (name : String) (arguments : List Argument) : Effect :=
  match space.lookupGlobal name with
  | none => ⟨.error (.raised (.runtime (.nameError name))), []⟩
  | some callee =>
    let (values, calls) := observeArguments space arguments
    match values with
    | .error error => ⟨.error error, calls⟩
    | .ok values =>
      let observed := Core.Module.SeededCall.invokeObserved callee values
      ⟨observed.result.bind (acceptCall destination), calls ++ [⟨name, observed⟩]⟩

inductive EvaluatesArguments (space : Namespace) :
    List Argument → Except Failure (List Value) → List CallEvent → Prop where
  | nil : EvaluatesArguments space [] (.ok []) []
  | stop {argument rest error calls}
      (failed : observeArgument space argument = (.error error, calls)) :
      EvaluatesArguments space (argument :: rest) (.error error) calls
  | next {argument rest value calls values later}
      (evaluated : observeArgument space argument = (.ok value, calls))
      (tail : EvaluatesArguments space rest values later) :
      EvaluatesArguments space (argument :: rest) (values.map (value :: ·)) (calls ++ later)

def assertOperand {scope : Scope} (space : Namespace) (operand : ModuleEntry.Operand scope)
    (expected : Bool) : Effect :=
  let checked := ((lowerScalarOperand operand).eval space #v[]).bind (assertTruthAs expected)
  ⟨checked.map fun _ => none, []⟩

def effect {scope : Scope} (space : Namespace) : Instruction scope → Effect
  | .scalar (.assign name _ operand) =>
    ⟨((lowerScalarOperand operand).eval space #v[]).map fun value => some (name, value), []⟩
  | .scalar (.assertion operand) => assertOperand space operand true
  | .assertNot operand => assertOperand space operand false
  | .publish .. => ⟨.error .unsupported, []⟩
  | .call destination name arguments =>
    let event := observeNamedCall space name arguments
    ⟨event.observation.result.bind (acceptCall destination), [event]⟩
  | .nestedCall destination name arguments => observeNestedCall space destination name arguments

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
    | .error error => ⟨space, .error error, item.calls⟩
    | .ok binding =>
      let updated := binding.elim space fun (name, value) => space.bindGlobal name value
      let tail := runInstructions updated rest
      { tail with calls := item.calls ++ tail.calls }

/-- Seeded execution starts from the same compiled instruction stream as
ordinary module execution. The caller supplies the namespace explicitly. -/
def run {source : Source.Module} (space : Namespace) (compiled : Compiled source) : Observation :=
  runInstructions space compiled.instructions

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
