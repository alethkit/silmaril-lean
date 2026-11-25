module

public import Silmaril.Languages.Starlark.Functions.Arguments.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists
open Lists.Iteration (Cursor iterationSource truth)

def typeName : Lists.Value → String
  | .scalar .none => "NoneType"
  | .scalar (.bool _) => "bool"
  | .scalar (.int _) => "int"
  | .string _ => "string"
  | .range _ => "range"
  | .list _ => "list"
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .function _ => "function"
  | .builtin _ => "builtin_function_or_method"

def minArity : Builtin → Nat
  | .len | .type | .range => 1
  | .bool | .list | .tuple => 0

def arityError (id : Builtin) (supplied : Nat) : Error :=
  .builtinArity id (minArity id) (if id = .range then 3 else 1) supplied

def rangeInteger : Lists.Value → Except Error Int
  | .scalar (.int i) => .ok i
  | value => .error (.builtinType .range value)

/-- Check the normalized constructor operands in positional order. -/
def checkedRange (start stop step : Lists.Value) : Except Error Lists.Value := do
  let first ← rangeInteger start
  let last ← rangeInteger stop
  let stride ← rangeInteger step
  if h : stride = 0 then throw .zeroRangeStep
  else pure (.range ⟨first, last, stride, h⟩)

def rangeArgs : List Lists.Value → Except Error Lists.Value
  | [stop] => checkedRange (.scalar (.int 0)) stop (.scalar (.int 1))
  | [start, stop] => checkedRange start stop (.scalar (.int 1))
  | [start, stop, step] => checkedRange start stop step
  | args => .error (arityError .range args.length)

/-- Read a collection snapshot or collect a range cursor in order. This
operation runs no Starlark code and leaves iterator guards alone. -/
def items (id : Builtin) : Lists.Value → Meaning (List Lists.Value)
  | value@(.list _) | value@(.tuple _) | value@(.dict _) =>
    Prod.snd <$> iterationSource value
  | .range span => pure (Cursor.ofRange span).collect
  | value => throw (.builtinType id value)

def countValue (count : Nat) : Lists.Value := .scalar (.int (Int.ofNat count))
def boolValue (value : Bool) : Lists.Value := .scalar (.bool value)

def unary : Builtin → Lists.Value → Meaning Lists.Value
  | .bool, value => boolValue <$> truth value
  | .len, .string text => pure (countValue text.utf8ByteSize)
  | .len, .range span => pure (countValue span.length)
  | .len, value => (countValue ∘ List.length) <$> items .len value
  | .type, value => pure (.string (typeName value))
  | .list, value => items .list value >>= allocate
  | .tuple, value => items .tuple value >>= allocateTuple
  | .range, value => fromExcept (rangeArgs [value])

/-- Apply a universal built-in to expanded arguments. All accept only
positional arguments, and keyword rejection precedes the other checks. -/
def invoke (id : Builtin) (actual : Actual) : Meaning Lists.Value :=
  match id, actual.keywords, actual.positional with
  | _, (name, _) :: _, _ => throw (.builtinKeyword id name)
  | _, [], [value] => unary id value
  | _, [], [] =>
    match id with
    | .bool => pure (boolValue false)
    | .list => allocate []
    | .tuple => allocateTuple []
    | .len | .type | .range => throw (arityError id 0)
  | .range, [], values@(_ :: _ :: _) => fromExcept (rangeArgs values)
  | _, [], _ :: _ :: _ => throw (arityError id actual.positional.length)

end Silmaril.Languages.Starlark.Functions.Builtins
