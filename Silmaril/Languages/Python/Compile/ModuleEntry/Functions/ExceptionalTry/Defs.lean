module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # Reached completion and cleanup for checked module suites -/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry

structure Plan (action : Type) where
  body : List action
  handler : Option (List action)
  otherwise : List action
  cleanup : List action

structure Outcome (state failure : Type) where
  reached : state
  completion : Except failure Unit

/-- Settle each successful scalar action before evaluating the next.
The failed action contributes no write and leaves the earlier state available. -/
def runSuite {state failure action : Type} (step : state → action → Except failure state) :
    state → List action → Outcome state failure
  | state, [] => ⟨state, .ok ()⟩
  | state, action :: rest =>
    match step state action with
    | .ok reached => runSuite step reached rest
    | .error error => ⟨state, .error error⟩

def Outcome.canEnterCleanup {state failure : Type} (outcome : Outcome state failure)
    (isPythonError : failure → Bool) : Bool :=
  match outcome.completion with
  | .ok () => true
  | .error failure => isPythonError failure

/-- Normal cleanup preserves the pending completion. A cleanup error takes
precedence with the state reached by that cleanup. -/
def Outcome.afterCleanup {state failure : Type} (pending cleaned : Outcome state failure) :
    Outcome state failure :=
  match cleaned.completion with
  | .ok () => ⟨cleaned.reached, pending.completion⟩
  | .error _ => cleaned

def afterBody {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (body : Outcome state failure) (handler : Option (List action))
    (otherwise : List action) : Outcome state failure :=
  match body.completion, handler with
  | .ok (), _ => suite body.reached otherwise
  | .error failure, some arm => if isPythonError failure then suite body.reached arm else body
  | .error _, none => body

def runCleanup {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (pending : Outcome state failure)
    (cleanup : List action) : Outcome state failure :=
  if pending.canEnterCleanup isPythonError then
    pending.afterCleanup (suite pending.reached cleanup)
  else pending

def run {state failure action : Type} (suite : state → List action → Outcome state failure)
    (isPythonError : failure → Bool) (initial : state) (plan : Plan action) : Outcome state failure :=
  let body := suite initial plan.body
  let pending := afterBody suite isPythonError body plan.handler plan.otherwise
  runCleanup suite isPythonError pending plan.cleanup

open Source (ExceptHandler Expr Name Scope Stmt)
open Core.Closure (RuntimeError)

def scalarAtom : Expr → Bool
  | .name _ => true
  | source => (exactScalarLiteral? source).isSome

def scalarStatement : Stmt → Bool
  | .pass => true
  | .assert_ condition none => scalarAtom condition
  | statement =>
    match binding? statement with
    | some checked => scalarAtom checked.val.2
    | none => false

inductive RaiseArgument (scope : Scope) where
  | text (value : Core.Text)
  | read (name : Name) (reference : GlobalReference scope name)

inductive RaiseArgument.Translation (scope : Scope) : Expr → RaiseArgument scope → Prop where
  | text {points value} (checked : Core.Text.ofPoints? points = some value) :
      Translation scope (.text points) (.text value)
  | read (name : Name) (reference : GlobalReference scope name) :
      Translation scope (.name name) (.read name reference)

def raiseArgument? (scope : Scope) :
    (source : Expr) → Option {value // RaiseArgument.Translation scope source value}
  | .text points =>
    match checked : Core.Text.ofPoints? points with
    | some value => some ⟨.text value, .text checked⟩
    | none => none
  | .name name =>
    (globalReference? scope name).map fun reference => ⟨.read name reference, .read name reference⟩
  | _ => none

structure RaiseCall (scope : Scope) where
  name : Name
  reference : GlobalReference scope name
  argument : RaiseArgument scope

inductive RaiseCall.Translation (scope : Scope) : Stmt → RaiseCall scope → Prop where
  | positional {name reference source argument} (checked : RaiseArgument.Translation scope source argument) :
      Translation scope (.raise_ (some (.callWith (.name name) [(.positional, source)])) none)
        ⟨name, reference, argument⟩
  | plain {name reference source argument} (checked : RaiseArgument.Translation scope source argument) :
      Translation scope (.raise_ (some (.call (.name name) [source])) none) ⟨name, reference, argument⟩

def raiseCall? (scope : Scope) : (source : Stmt) → Option {call // RaiseCall.Translation scope source call}
  | .raise_ (some (.callWith (.name name) [(.positional, source)])) none => do
    let reference ← globalReference? scope name
    let checked ← raiseArgument? scope source
    return ⟨⟨name, reference, checked.val⟩, .positional checked.property⟩
  | .raise_ (some (.call (.name name) [source])) none => do
    let reference ← globalReference? scope name
    let checked ← raiseArgument? scope source
    return ⟨⟨name, reference, checked.val⟩, .plain checked.property⟩
  | _ => none

inductive RaiseCallee where
  | stockException
  | nonCallable
  | outsideProfile

def RaiseArgument.eval {scope : Scope} {Value : Type} (lookup : Name → Option Value)
    (text? : Value → Option Core.Text) : RaiseArgument scope → Except RuntimeError (Option Core.Text)
  | .text value => .ok (some value)
  | .read name _ => (lookup name).elim (.error (.nameError name)) (.ok ∘ text?)

def RaiseCallee.construct : RaiseCallee → Option Core.Text → Option RuntimeError
  | .stockException, argument => argument.map .explicitException
  | .nonCallable, _ => some .notCallable
  | .outsideProfile, _ => none

/-- Save the live callee before reading the argument. Dispatch occurs only
after the argument succeeds. The constructed exception is immediately raised. -/
def RaiseCall.error {scope : Scope} {Value : Type} (call : RaiseCall scope)
    (lookup : Name → Option Value) (classify : Value → RaiseCallee) (text? : Value → Option Core.Text) :
    Option RuntimeError :=
  match lookup call.name with
  | none => some (.nameError call.name)
  | some callee =>
    match call.argument.eval lookup text? with
    | .error error => some error
    | .ok argument => (classify callee).construct argument

inductive Step (scope : Scope) where
  | scalar (action : Action scope)
  | raiseCall (call : RaiseCall scope)

inductive Suite (scope : Scope) : List Stmt → List (Step scope) → Prop where
  | nil : Suite scope [] []
  | scalar {source rest actions tail} (allowed : scalarStatement source = true)
      (code : ModuleEntry.Translation scope [source] actions)
      (remaining : Suite scope rest tail) :
      Suite scope (source :: rest) ((actions.map (Step.scalar ∘ Action.inLiteralArm)) ++ tail)
  | raiseCall {source rest call tail} (checked : RaiseCall.Translation scope source call)
      (remaining : Suite scope rest tail) :
      Suite scope (source :: rest) (.raiseCall call :: tail)

def suite? (scope : Scope) : (source : List Stmt) → Option {actions // Suite scope source actions}
  | [] => some ⟨[], .nil⟩
  | statement :: rest => do
    let tail ← suite? scope rest
    if allowed : scalarStatement statement = true then
      let lowered ← (lowerStatements scope [statement]).toOption
      return ⟨lowered.val.map (Step.scalar ∘ Action.inLiteralArm) ++ tail.val,
        .scalar allowed lowered.property tail.property⟩
    else
      let checked ← raiseCall? scope statement
      return ⟨.raiseCall checked.val :: tail.val, .raiseCall checked.property tail.property⟩

inductive Handler (scope : Scope) : List ExceptHandler → List Stmt → List Stmt →
    Option (List (Step scope)) → Prop where
  | finallyOnly {cleanup} (present : cleanup.isEmpty = false) :
      Handler scope [] [] cleanup none
  | bare {source otherwise cleanup actions} (present : source.isEmpty = false)
      (translated : Suite scope source actions) :
      Handler scope [⟨none, none, source⟩] otherwise cleanup (some actions)

def handler? (scope : Scope) : (handlers : List ExceptHandler) → (otherwise cleanup : List Stmt) →
    Option {handler // Handler scope handlers otherwise cleanup handler}
  | [], [], cleanup =>
    if present : cleanup.isEmpty = false then some ⟨none, .finallyOnly present⟩ else none
  | [⟨none, none, source⟩], _, _ =>
    if present : source.isEmpty = false then
      (suite? scope source).map fun checked => ⟨some checked.val, .bare present checked.property⟩
    else none
  | _, _, _ => none

inductive Translation (scope : Scope) : Stmt → Plan (Step scope) → Prop where
  | checked {body handlers otherwise cleanup first handler normal final}
      (present : body.isEmpty = false) (bodyCode : Suite scope body first)
      (handlerCode : Handler scope handlers otherwise cleanup handler)
      (elseCode : Suite scope otherwise normal) (cleanupCode : Suite scope cleanup final) :
      Translation scope (.try_ body handlers otherwise cleanup) ⟨first, handler, normal, final⟩

def check (scope : Scope) : (source : Stmt) → Option {plan // Translation scope source plan}
  | .try_ body handlers otherwise cleanup =>
    if present : body.isEmpty = false then do
      let first ← suite? scope body
      let handler ← handler? scope handlers otherwise cleanup
      let normal ← suite? scope otherwise
      let final ← suite? scope cleanup
      return ⟨⟨first.val, handler.val, normal.val, final.val⟩,
        .checked present first.property handler.property normal.property final.property⟩
    else none
  | _ => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ExceptionalTry
