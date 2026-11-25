module

public import Silmaril.Languages.Starlark.Functions.Builtins.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Syntax.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite denoteSuite truth)

abbrev DeclarationId := Nat

def withoutDeclaration (available : List DeclarationId) (id : DeclarationId) : List DeclarationId :=
  available.filter (· != id)

/-- Resolved function code with direct expression operands. -/
inductive Body where
  | total (code : Suite 0)
  | returnExpr (value : Lowering.Expr)
  | assignExpr (target : Binding) (value : Lowering.Expr)
  | seq (first rest : Body)
  | branch (test : Lists.Expr) (yes no : Body)
  | branchExpr (test : Lowering.Expr) (yes no : Body)
  | forIn (target : Binding) (iterable : Lists.Expr) (body : Body)
  | forInExpr (target : Binding) (iterable : Lowering.Expr) (body : Body)
  | breakLoop
  | continueLoop
  | define (target : Binding) (declaration : DeclarationId)
  | call (target : Option Binding) (callee : Lists.Expr) (arguments : Arguments)

/-- Capture a slot from the defining activation under its resolved name in the callee. -/
structure FreeName where
  source : Binding
  target : Binding

structure Declaration where
  signature : Signature
  locals : List Binding
  free : List FreeName
  body : Body

/-- Declaration indices are stable across different activations of the same `def`. -/
abbrev Program := Array Declaration

def captureName (state : State) (name : FreeName) : Except Error Capture :=
  match state.slots name.source with
  | none => .error (.missingCapture name.source)
  | some (.owned address) => .ok ⟨name.target, address, name.source.scope == .local⟩
  | some (.captured address localCell) => .ok ⟨name.target, address, localCell⟩

def defaultOperands (program : Program) (id : DeclarationId) : Code (List Lists.Value) :=
  operandList ((program[id]?.toList.flatMap fun declaration =>
    declaration.signature.defaulted.map Prod.snd))

def define (program : Program) (target : Binding) (id : DeclarationId)
    (defaults : List Lists.Value) : Meaning Flow :=
  fun state =>
    match program[id]? with
    | none => .error (.unknownDeclaration id) state
    | some declaration =>
      match declaration.free.mapM (captureName state) with
      | .error error => .error error state
      | .ok captures =>
        let address := state.heap.size
        let boundDefaults := (declaration.signature.defaulted.map Prod.fst).zip defaults
        let next := { state with
          heap := state.heap.push ⟨.function ⟨id, captures, boundDefaults⟩, false⟩ }
        .ok .next (next.write target (.function address))

def getClosure (address : Address) : Meaning Closure :=
  projectCell address fun
    | .function closure => some closure
    | _ => none

def capturedSlots (captures : List Capture) (binding : Binding) : Option Slot :=
  (captures.find? fun capture => capture.binding == binding).map
    fun capture => .captured capture.address capture.localCell

def activate (state : State) (declaration : Declaration) (captures : List Capture)
    (arguments : List (Binding × Lists.Value)) : State :=
  let frame := { state with bindings := fun _ => none, slots := capturedSlots captures }
  let frame := (declaration.signature.slots ++ declaration.locals).foldl State.allocateSlot frame
  arguments.foldl (fun next (binding, value) =>
    next.write binding value) frame

structure Prepared (available : List DeclarationId) where
  id : DeclarationId
  permitted : id ∈ available
  body : Body

inductive CallPlan (available : List DeclarationId) where
  | closure (prepared : Prepared available)
  | builtin (id : Builtin) (actual : Actual)

def prepareExpanded (program : Program) (available : List DeclarationId) (actual : Actual) :
    Lists.Value → Meaning (CallPlan available)
  | .builtin id => pure (.builtin id actual)
  | .function address => do
    let closure ← getClosure address
    match program[closure.declaration]? with
    | none => throw (.unknownDeclaration closure.declaration)
    | some declaration =>
      if h : closure.declaration ∈ available then do
        let bound ← fromExcept (bindArguments declaration.signature closure.defaults actual)
        let assigned ← packArgs declaration.signature bound
        fun state =>
          .ok (.closure ⟨closure.declaration, h, declaration.body⟩)
            (activate state declaration closure.captures assigned)
      else throw (.recursiveCall closure.declaration)
  | _ => throw .notCallable

/-- Expand evaluated operands before callability, then check re-entry before binding. -/
def prepare (program : Program) (available : List DeclarationId) (arguments : Arguments) :
    List Lists.Value → Meaning (CallPlan available)
  | callee :: operands => do
    let actual ← arguments.expand operands
    prepareExpanded program available actual callee
  | [] => throw .notCallable

def Body.validateIn (inLoop : Bool) : Body → Except CallStaticError Unit
  | .seq first rest => do
    first.validateIn inLoop
    rest.validateIn inLoop
  | .branch _ yes no => do
    yes.validateIn inLoop
    no.validateIn inLoop
  | .branchExpr test yes no => do
    test.validateCalls
    yes.validateIn inLoop
    no.validateIn inLoop
  | .forIn _ _ body => body.validateIn true
  | .forInExpr _ iterable body => do
    iterable.validateCalls
    body.validateIn true
  | .breakLoop => if inLoop then pure () else throw .breakOutsideLoop
  | .continueLoop => if inLoop then pure () else throw .continueOutsideLoop
  | .call _ _ arguments => arguments.validate
  | .returnExpr value | .assignExpr _ value => value.validateCalls
  | .define .. | .total _ => pure ()

def Body.validateCalls (body : Body) : Except CallStaticError Unit := body.validateIn false

def validate (program : Program) (body : Body) : Except CallStaticError Unit := do
  for declaration in program do
    declaration.signature.validate
    declaration.body.validateCalls
  body.validateCalls

def restoreCaller (caller state : State) : State :=
  { state with slots := caller.slots, bindings := caller.bindings }

def writeCallResult (target : Option Binding) (value : Lists.Value) : Meaning Flow :=
  fun state => .ok .next (target.elim state fun binding => state.write binding value)

def completeCall (caller : State) (target : Option Binding) : Outcome Flow → Outcome Flow
  | .error error state => .error error (restoreCaller caller state)
  | .ok flow state =>
    let value := match flow with
      | .returned result => result
      | _ => .scalar .none
    writeCallResult target value (restoreCaller caller state)

end Silmaril.Languages.Starlark.Functions
