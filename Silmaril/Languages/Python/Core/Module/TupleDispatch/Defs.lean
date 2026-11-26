module

public import Silmaril.Languages.Python.Core.Module.Defs

/-! # Exact tuple methods on flat scalar contents -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.TupleDispatch

/-- An absent address represents the canonical empty tuple. Other addresses
belong to this evaluation's table of immutable tuple objects. -/
structure Object where
  address : Option Nat
  contents : List Core.Module.Value
  deriving DecidableEq, Repr

structure Heap where
  objects : Array (List Core.Module.Value)
  deriving DecidableEq, Repr

def Heap.empty : Heap := ⟨#[]⟩

def Heap.materialize (heap : Heap) (contents : List Core.Module.Value) : Object × Heap :=
  match contents with
  | [] => (⟨none, []⟩, heap)
  | _ :: _ => (⟨some heap.objects.size, contents⟩, ⟨heap.objects.push contents⟩)

def concat (heap : Heap) (left right : Object) : Object × Heap :=
  if left.contents.isEmpty then (right, heap)
  else if right.contents.isEmpty then (left, heap)
  else heap.materialize (left.contents ++ right.contents)

def equalContents (left right : List Core.Module.Value) : Bool :=
  left.isEqv right Core.Module.Value.equal

inductive Literal where
  | tuple (contents : List Core.Module.Value)
  | list (contents : List Core.Module.Value)
  deriving DecidableEq, Repr

inductive Operand where
  | tuple (object : Object)
  | list (contents : List Core.Module.Value)
  deriving DecidableEq, Repr

def Literal.prepare (heap : Heap) : Literal → Operand × Heap
  | .tuple contents =>
    let (object, reached) := heap.materialize contents
    (.tuple object, reached)
  | .list contents => (.list contents, heap)

def equal (left : Object) : Operand → Bool
  | .tuple right => equalContents left.contents right.contents
  | .list _ => false

inductive Method where
  | add
  | eq
  deriving DecidableEq, Repr

def Method.name : Method → String
  | .add => "__add__"
  | .eq => "__eq__"

inductive Failure where
  | missingType
  | missingAttribute (method : Method)
  | wrongReceiver (method : Method)
  | wrongArgument
  | unsupported
  deriving DecidableEq, Repr

inductive Result where
  | tuple (object : Object)
  | bool (value : Bool)
  | notImplemented
  deriving DecidableEq, Repr

structure BoundMethod where
  method : Method
  receiver : Object

structure UnboundMethod where
  method : Method
  deriving DecidableEq, Repr

/-- A stock tuple type token comes from the live module-first lookup. The
other explicit case is the exact None singleton with no such attribute. -/
inductive TypeBinding where
  | stockTuple
  | noneValue
  | outsideProfile
  deriving DecidableEq

def lookupUnbound (binding : Option TypeBinding) (method : Method) : Except Failure UnboundMethod :=
  match binding with
  | none => .error .missingType
  | some .stockTuple => .ok ⟨method⟩
  | some .noneValue => .error (.missingAttribute method)
  | some .outsideProfile => .error .unsupported

def BoundMethod.invoke (bound : BoundMethod) (heap : Heap) (argument : Operand) :
    Except Failure Result × Heap :=
  match bound.method, argument with
  | .add, .tuple right =>
    let (object, reached) := concat heap bound.receiver right
    (.ok (.tuple object), reached)
  | .add, .list _ => (.error .wrongArgument, heap)
  | .eq, .tuple right => (.ok (.bool (equal bound.receiver (.tuple right))), heap)
  | .eq, .list _ => (.ok .notImplemented, heap)

def UnboundMethod.invoke (unbound : UnboundMethod) (heap : Heap) (receiver argument : Operand) :
    Except Failure Result × Heap :=
  match receiver with
  | .tuple object => (BoundMethod.mk unbound.method object).invoke heap argument
  | .list _ => (.error (.wrongReceiver unbound.method), heap)

/-- The exact literal receiver is evaluated and bound before the argument. -/
def callBound (heap : Heap) (method : Method) (receiver : List Core.Module.Value)
    (argument : Literal) : Except Failure Result × Heap :=
  let (object, boundHeap) := heap.materialize receiver
  let bound : BoundMethod := ⟨method, object⟩
  let (value, reached) := argument.prepare boundHeap
  bound.invoke reached value

/-- Resolve the exact type descriptor, then prepare both positional arguments
in order. Receiver type checking belongs to invocation. -/
def callUnbound (heap : Heap) (binding : Option TypeBinding) (method : Method)
    (receiver argument : Literal) : Except Failure Result × Heap :=
  match lookupUnbound binding method with
  | .error error => (.error error, heap)
  | .ok unbound =>
    let (object, receiverHeap) := receiver.prepare heap
    let (value, reached) := argument.prepare receiverHeap
    unbound.invoke reached object value

end Silmaril.Languages.Python.Core.Module.TupleDispatch
