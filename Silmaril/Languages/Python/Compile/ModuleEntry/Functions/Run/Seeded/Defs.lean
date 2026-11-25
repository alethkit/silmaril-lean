module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Defs
public import Silmaril.Languages.Python.Core.Module.SeededCall.Observation.Defs

/-! # Run checked module-call instructions with an explicit closed seed -/

@[expose] public section

namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded

open Source (Scope)
open Core.Closure (Function Heap)
open Core.Closure.Executor (CodeTable Fault)
open Core.Module.SeededCall (AssertionArgument Bindings CallObservation Expectation Failure Namespace Raised Result Value)

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

def scalar? : Value → Option Core.Module.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none | .exceptionClass _ | .helper _ | .function _ => none

/-- Boolean literals are admitted inside equality. The resulting Boolean
can be bound as a value. Other compound operands use the existing boundary. -/
def evaluateScalar {scope : Scope} (space : Namespace) (equalityOperand : Bool) :
    ModuleEntry.Operand scope → Result
  | .binary .equal left right => do
    let first ← evaluateScalar space true left
    let second ← evaluateScalar space true right
    let some first := scalar? first | throw .unsupported
    let some second := scalar? second | throw .unsupported
    return .bool (first.equal second)
  | .boolean value =>
    if equalityOperand then .ok (.bool value) else .error .unsupported
  | operand => (lowerScalarOperand operand).eval space #v[]

def truth : Value → Bool
  | .int value => decide (value ≠ 0)
  | .bool value => value
  | .none => false
  | .exceptionClass _ | .helper _ => true
  | .function closure => (Core.Closure.Value.function closure).truth

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

/-- Executor faults and live prefixes are outside Python exception delivery. -/
inductive ModuleFailure where
  | raised (error : Raised)
  | unsupported
  | publicationFault (error : Core.Closure.Dispatch.Failure)
  | callbackFault (fault : Fault)
  | callbackFuelExhausted
  deriving DecidableEq, Repr

def ModuleFailure.ofCall : Failure → ModuleFailure
  | .raised error => .raised error
  | .unsupported => .unsupported

structure Effect where
  binding : Except ModuleFailure (Option (String × Value))
  calls : List CallEvent

def ordinaryValue? : Value → Option Core.Closure.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none => some .none
  | .function closure => some (.function closure)
  | .exceptionClass _ | .helper _ => none

def seededValue : Core.Closure.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none
  | .function closure => .function closure

def callbackSession (space : Namespace) (heap : Heap) : Core.Module.Functions.Session :=
  ⟨fun name => (space.lookupGlobal name).bind ordinaryValue?, heap⟩

def callbackInvocation (space : Namespace) (heap : Heap) (closure : Function) :
    Core.Module.Functions.Invocation :=
  (callbackSession space heap).prepareCall .discard (.literal (.function closure)) []

/-- The ordinary executor delivers an ambient lookup miss as a terminal
`nameError name`. Check the same namespace before passing it to the
expectation, since projection also drops seed-only values. -/
def callbackError (space : Namespace) (error : Core.Closure.RuntimeError) : Failure :=
  match error with
  | .nameError name =>
    match space.lookupGlobal name with
    | none => .raised (.runtime error)
    | some value =>
      if (ordinaryValue? value).isNone then .unsupported else .raised (.runtime error)
  | .assertionError => .raised (.assertionError .empty)
  | _ => .raised (.runtime error)

/-- Deliver only a completed ordinary callback to the existing expectation.
All ordinary states carry the exact heap at that point in execution. -/
def observeCallback (space : Namespace) (expectation : Expectation) :
    Core.Closure.Executor.State → Except ModuleFailure CallObservation × Heap
  | .finished heap result =>
    let inner := (result.map seededValue).mapError (callbackError space)
    (.ok ⟨expectation.deliver inner, expectation.caught? inner⟩, heap)
  | .faulted heap _ fault => (.error (.callbackFault fault), heap)
  | .running heap .. | .delivering heap .. | .receiving heap .. =>
    (.error .callbackFuelExhausted, heap)

structure CallContext where
  table : CodeTable
  heap : Heap
  fuel : Nat
  published : List Function := []

def invokeCallback (space : Namespace) (context : CallContext)
    (expectation : Expectation) (closure : Function) : Except ModuleFailure CallObservation × Heap :=
  let invocation := callbackInvocation space context.heap closure
  observeCallback space expectation (invocation.runPrefix context.table context.fuel).2.state

def invokeCall (space : Namespace) (context : CallContext) (callee : Value) (arguments : List Value) :
    Except ModuleFailure CallObservation × Heap :=
  match Core.Module.SeededCall.Request.decode callee arguments with
  | .expect expectation (.function closure) [] _ =>
    let unsupported := (.ok ⟨.error .unsupported, none⟩, context.heap)
    if closure ∈ context.published then
      match Core.Closure.Dispatch.resolve context.table closure.code with
      | .ok definition =>
        if definition.parameters.slots.isEmpty then invokeCallback space context expectation closure
        else unsupported
      | .error _ => invokeCallback space context expectation closure
    else unsupported
  | _ => (.ok (Core.Module.SeededCall.invokeObserved callee arguments), context.heap)

def acceptObservation (destination : Core.Module.Functions.Destination)
    (name : String) (observed : CallObservation) : Effect :=
  ⟨(observed.result.bind (acceptCall destination)).mapError ModuleFailure.ofCall, [⟨name, observed⟩]⟩

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
    | .error error => ⟨.error (.ofCall error), calls⟩
    | .ok values =>
      let observed := Core.Module.SeededCall.invokeObserved callee values
      ⟨(observed.result.bind (acceptCall destination)).mapError ModuleFailure.ofCall,
        calls ++ [⟨name, observed⟩]⟩

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
  let checked := (evaluateScalar space false operand).bind (assertTruthAs expected)
  ⟨(checked.map fun _ => none).mapError ModuleFailure.ofCall, []⟩

def effect {scope : Scope} (space : Namespace) (context : CallContext) (instruction : Instruction scope) :
    Effect × Heap :=
  match instruction with
  | .scalar (.assign name _ operand) =>
    (⟨((evaluateScalar space false operand).map fun value => some (name, value)).mapError ModuleFailure.ofCall,
      []⟩, context.heap)
  | .scalar (.assertion operand) => (assertOperand space operand true, context.heap)
  | .assertNot operand => (assertOperand space operand false, context.heap)
  | .publish name function =>
    let resolved := Core.Closure.Dispatch.resolve context.table function.ref
    (⟨(resolved.map fun _ => some (name, .function function.closure)).mapError .publicationFault, []⟩, context.heap)
  | .call destination name arguments =>
    match Core.Module.SeededCall.resolveCall space #v[] (.global name) (arguments.map lowerCallOperand) with
    | .error error => (acceptObservation destination name ⟨.error error, none⟩, context.heap)
    | .ok (callee, values) =>
      let (observed, heap) := invokeCall space context callee values
      match observed with
      | .ok result => (acceptObservation destination name result, heap)
      | .error error => (⟨.error error, []⟩, heap)
  | .nestedCall destination name arguments => (observeNestedCall space destination name arguments, context.heap)

structure Observation where
  residual : Namespace
  completion : Except ModuleFailure Unit
  calls : List CallEvent
  heap : Heap

/-- A failed instruction keeps its incoming namespace and the heap reached
by its effects. Only successful publications authorize ordinary callbacks. -/
def runInstructionsIn {scope : Scope} (space : Namespace) (context : CallContext) :
    List (Instruction scope) → Observation
  | [] => ⟨space, .ok (), [], context.heap⟩
  | instruction :: rest =>
    let (item, heap) := effect space context instruction
    match item.binding with
    | .error error => ⟨space, .error error, item.calls, heap⟩
    | .ok binding =>
      let updated := binding.elim space fun (name, value) => space.bindGlobal name value
      let published := match instruction with
        | .publish _ function => function.closure :: context.published
        | _ => context.published
      let tail := runInstructionsIn updated { context with heap, published } rest
      { tail with calls := item.calls ++ tail.calls }

def runInstructions {scope : Scope} (space : Namespace) (instructions : List (Instruction scope))
    (table : CodeTable := fun _ => none) (heap : Heap := .empty) (callbackFuel : Nat := 1000) : Observation :=
  runInstructionsIn space ⟨table, heap, callbackFuel, []⟩ instructions

/-- Seeded execution starts from the same compiled instruction stream as
ordinary module execution. The caller supplies the namespace explicitly. -/
def run {source : Source.Module} (space : Namespace) (compiled : Compiled source)
    (heap : Heap := .empty) (callbackFuel : Nat := 1000) : Observation :=
  runInstructions space compiled.instructions compiled.table heap callbackFuel

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded
