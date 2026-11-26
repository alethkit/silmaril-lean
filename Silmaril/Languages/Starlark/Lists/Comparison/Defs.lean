module

public import Silmaril.Languages.Starlark.Lists.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- A scan returns the first decisive Boolean or error. Exhaustion returns the
opposite Boolean. Tuple equality and membership differ only in what stops them. -/
def scan {α : Type} (test : α → Except Error Bool) (decisive : Bool) :
    List α → Except Error Bool
  | [] => .ok (!decisive)
  | item :: rest =>
    match test item with
    | .error error => .error error
    | .ok flag => if flag = decisive then .ok flag else scan test decisive rest

/-- The first tuple comparison starts with the pinned Go default. Each paired
field consumes one level. Membership starts a fresh comparison per element. -/
def defaultDepth : Nat := 10

/-- Classify the operands by type without reading any tuple cells. -/
inductive Pair where
  | scalars (left right : Starlark.Value)
  | strings (left right : String)
  | tuples (left right : Address)
  | different
  | unsupported

def Pair.ofValues : Value → Value → Pair
  | .scalar a, .scalar b => .scalars a b
  | .string a, .string b => .strings a b
  | .tuple a, .tuple b => .tuples a b
  | .scalar _, .string _ | .string _, .scalar _
  | .scalar _, .tuple _ | .tuple _, .scalar _
  | .string _, .tuple _ | .tuple _, .string _ => .different
  | _, _ => .unsupported

/-- The Boolean read by scalar `==`, including exact mixed numeric comparison. -/
def scalarEqual (left right : Starlark.Value) : Bool :=
  match left.orderedCompare right with
  | some order => order == .eq
  | none => left.isNone && right.isNone

/-- Compare at most the given number of levels, checking tuple lengths before
reading any field pair. The comparison reads fields from the left cell first. -/
def equalAt (heap : Heap) : Nat → Value → Value → Except Error Bool
  | 0, _, _ => .error .comparisonDepth
  | depth + 1, left, right =>
    match Pair.ofValues left right with
    | .scalars a b => .ok (scalarEqual a b)
    | .strings a b => .ok (decide (a = b))
    | .different => .ok false
    | .unsupported => .error (.comparisonType left right)
    | .tuples a b => do
      let xs ← heap.tupleFields a
      let ys ← heap.tupleFields b
      if xs.length = ys.length then
        scan (fun pair => equalAt heap depth pair.1 pair.2) false (xs.zip ys)
      else pure false

/-- Test a tuple's elements in order, using each element as the left operand. -/
def containsAt (heap : Heap) (depth : Nat) (needle : Value) : Value → Except Error Bool
  | .tuple address => do
    let fields ← heap.tupleFields address
    scan (fun field => equalAt heap depth field needle) true fields
  | other => .error (.membershipTarget other)

def evaluate (heap : Heap) (op : ComparisonOp) (left right : Value) : Except Error Bool :=
  match op with
  | .eq => equalAt heap defaultDepth left right
  | .ne => (! ·) <$> equalAt heap defaultDepth left right
  | .mem => containsAt heap defaultDepth left right
  | .notMem => (! ·) <$> containsAt heap defaultDepth left right

def finish (out : Except Error Bool) : Meaning Value :=
  fromExcept (out.map fun flag => .scalar (.bool flag))

def apply (op : ComparisonOp) (left right : Value) : Meaning Value := fun state =>
  finish (evaluate state.heap op left right) state

end Silmaril.Languages.Starlark.Lists.Comparison
