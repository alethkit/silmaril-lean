module

public import Silmaril.Languages.Starlark.Lists.Iteration.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions

open Lists
open Lists.Iteration (Flow Suite denoteSuite truth)

abbrev DeclarationId := Nat

def withoutDeclaration (available : List DeclarationId) (id : DeclarationId) : List DeclarationId :=
  available.filter (· != id)

/-- Resolved function code. Calls in expressions are lowered to calls with a
destination slot and subsequent uses of that slot. -/
inductive Body where
  | total (code : Suite 0)
  | seq (first rest : Body)
  | branch (test : Lists.Expr) (yes no : Body)
  | define (target : Binding) (declaration : DeclarationId)
  | call (target : Option Binding) (callee : Lists.Expr) (arguments : Code (List Lists.Value))

/-- Capture a slot from the defining activation under its resolved name in the callee. -/
structure FreeName where
  source : Binding
  target : Binding

structure Declaration where
  params : List Binding
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

def define (program : Program) (target : Binding) (id : DeclarationId) : Meaning Flow :=
  fun state =>
    match program[id]? with
    | none => .error (.unknownDeclaration id) state
    | some declaration =>
      match declaration.free.mapM (captureName state) with
      | .error error => .error error state
      | .ok captures =>
        let address := state.heap.size
        let next := { state with heap := state.heap.push ⟨.function ⟨id, captures⟩, false⟩ }
        .ok .next (next.write target (.function address))

def getClosure (address : Address) : Meaning Closure :=
  projectCell address fun
    | .function closure => some closure
    | _ => none

def capturedSlots (captures : List Capture) (binding : Binding) : Option Slot :=
  (captures.find? fun capture => capture.binding == binding).map
    fun capture => .captured capture.address capture.localCell

def activate (state : State) (declaration : Declaration) (captures : List Capture)
    (arguments : List Lists.Value) : State :=
  let frame := { state with bindings := fun _ => none, slots := capturedSlots captures }
  let frame := (declaration.params ++ declaration.locals).foldl State.allocateSlot frame
  (declaration.params.zip arguments).foldl (fun next (binding, value) =>
    next.write binding value) frame

structure Prepared (available : List DeclarationId) where
  id : DeclarationId
  permitted : id ∈ available
  body : Body

/-- The caller evaluates every operand before checking callable identity and
arity. Removing a declaration from `available` protects all of its instances. -/
def prepare (program : Program) (available : List DeclarationId) :
    List Lists.Value → Meaning (Prepared available)
  | .function address :: arguments => do
    let closure ← getClosure address
    fun state =>
      match program[closure.declaration]? with
      | none => .error (.unknownDeclaration closure.declaration) state
      | some declaration =>
        if h : closure.declaration ∈ available then
          if declaration.params.length = arguments.length then
            .ok ⟨closure.declaration, h, declaration.body⟩
              (activate state declaration closure.captures arguments)
          else .error (.arity declaration.params.length arguments.length) state
        else .error (.recursiveCall closure.declaration) state
  | _ => throw .notCallable

def restoreCaller (caller state : State) : State :=
  { state with slots := caller.slots, bindings := caller.bindings }

def completeCall (caller : State) (target : Option Binding) : Outcome Flow → Outcome Flow
  | .error error state => .error error (restoreCaller caller state)
  | .ok flow state =>
    let value := match flow with
      | .returned result => result
      | _ => .scalar .none
    let state := restoreCaller caller state
    .ok .next (target.elim state fun binding => state.write binding value)

end Silmaril.Languages.Starlark.Functions
