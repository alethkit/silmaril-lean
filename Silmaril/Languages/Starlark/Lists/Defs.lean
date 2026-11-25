module

public import Silmaril.Languages.Starlark.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists

/-- An index in the shared heap. Allocation appends a fresh cell. -/
abbrev Address := Nat

inductive Value where
  | scalar (value : Starlark.Value)
  | list (address : Address)
  deriving DecidableEq, Repr

def Value.address? : Value → Option Address
  | .list address => some address
  | .scalar _ => none

structure Cell where
  elements : List Value
  frozen : Bool := false
  deriving DecidableEq, Repr

abbrev Heap := Array Cell

structure State where
  heap : Heap := #[]
  bindings : Binding → Option Value := fun _ => none

inductive Error where
  | uninitialized (binding : Binding)
  | danglingAddress (address : Address)
  | indexTarget
  | indexType
  | indexRange (index : Int) (length : Nat)
  | assignmentTarget
  | appendTarget
  | frozen (address : Address)
  deriving DecidableEq, Repr

abbrev Outcome := EStateM.Result Error State
abbrev Meaning := EStateM Error State

/-- Apply one primitive to an operand result, preserving its state on failure. -/
def Outcome.resume {α β : Type} (out : Outcome α) (primitive : α → Meaning β) : Outcome β :=
  match out with
  | .ok value state => primitive value state
  | .error error state => .error error state

def State.read (state : State) : Ref → Outcome Value
  | .predeclared value => .ok (.scalar value) state
  | .bound binding =>
    match state.bindings binding with
    | some value => .ok value state
    | none => .error (.uninitialized binding) state

def bindValue (binding : Binding) (value : Value) : Meaning Unit := fun state =>
  .ok () { state with bindings := fun key =>
    if key = binding then some value else state.bindings key }

def allocate (elements : List Value) : Meaning Value := fun state =>
  .ok (.list state.heap.size) { state with heap := state.heap.push ⟨elements, false⟩ }

def getCell (address : Address) : Meaning Cell := fun state =>
  match state.heap[address]? with
  | some cell => .ok cell state
  | none => .error (.danglingAddress address) state

/-- List indexes range from `-length` through `length - 1`. -/
def normalizeIndex (length : Nat) : Value → Except Error (Fin length)
  | .scalar (.int index) =>
    let offset := if index < 0 then (length : Int) + index else index
    if h : 0 ≤ offset ∧ offset.toNat < length then .ok ⟨offset.toNat, h.2⟩
    else .error (.indexRange index length)
  | _ => .error .indexType

def fromExcept {α : Type} : Except Error α → Meaning α
  | .ok value => pure value
  | .error error => throw error

def readIndex (receiver index : Value) : Meaning Value := do
  match receiver with
  | .scalar _ => throw .indexTarget
  | .list address =>
    let cell ← getCell address
    let i ← fromExcept (normalizeIndex cell.elements.length index)
    pure (cell.elements[i.val]'(i.isLt))

/-- Validate an edit against the current contents, then check mutability before committing. -/
def updateCell (address : Address) (edit : List Value → Except Error (List Value)) :
    Meaning Unit := do
  let cell ← getCell address
  let elements ← fromExcept (edit cell.elements)
  fun state =>
    if cell.frozen then .error (.frozen address) state
    else .ok () { state with heap :=
      state.heap.setIfInBounds address { cell with elements } }

def writeIndex (receiver index value : Value) : Meaning Unit := do
  match receiver with
  | .scalar _ => throw .assignmentTarget
  | .list address =>
    updateCell address fun elements => do
      let i ← normalizeIndex elements.length index
      pure (elements.set i.val value)

def appendAt (address : Address) (value : Value) : Meaning Value := do
  updateCell address fun elements => .ok (elements ++ [value])
  return .scalar .none

/-- Resolved syntax indexed by the type of its result. The list element spine,
expressions and statements share a structural recursion principle. -/
inductive Code : Type → Type where
  | scalar (value : Starlark.Value) : Code Value
  | read (ref : Ref) : Code Value
  | list (elements : Code (List Value)) : Code Value
  | empty : Code (List Value)
  | cons (head : Code Value) (tail : Code (List Value)) : Code (List Value)
  | index (receiver index : Code Value) : Code Value
  | append (receiver argument : Code Value) : Code Value
  | pass : Code Unit
  | eval (expr : Code Value) : Code Unit
  | assign (binding : Binding) (rhs : Code Value) : Code Unit
  | setIndex (receiver index rhs : Code Value) : Code Unit
  | seq (first rest : Code Unit) : Code Unit

abbrev Expr := Code Value
abbrev Stmt := Code Unit

end Silmaril.Languages.Starlark.Lists
