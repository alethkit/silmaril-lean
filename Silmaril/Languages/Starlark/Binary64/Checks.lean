module

import Silmaril.Languages.Starlark.Binary64.Thms
import Silmaril.Languages.Starlark.Denotation.Defs
import Silmaril.Languages.Starlark.Functions.Builtins.Thms
import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Numeric.Ieee754
meta import Silmaril.Languages.Starlark.Functions.Builtins.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs
meta import Silmaril.Languages.Starlark.Denotation.Defs

namespace Silmaril.Languages.Starlark.Binary64

open Functions (Arguments run)
open Functions.Builtins (invoke)
open Lists (Builtin Error Outcome State)
open Lists.Iteration (Flow finishState)

deriving instance DecidableEq for Except

private def value (bits : UInt64) : Lists.Value := .scalar (.float bits)

private def result {α : Type} : Outcome α → Except Error α
  | .ok value _ => .ok value
  | .error error _ => .error error

-- The small executable dependency exposes the same operation as the reusable IEEE model.
example (input : Numeric.Ieee754.F64) :
    (⟨abs input.bits⟩ : Numeric.Ieee754.F64) = input.abs := rfl

#guard
  let cases : List (UInt64 × UInt64 × Bool) := [
    (0, 0, false),
    (0x8000000000000000, 0, false),
    (0x8000000000000001, 1, true),
    (0xbff4000000000000, 0x3ff4000000000000, true),
    (0xffefffffffffffff, 0x7fefffffffffffff, true),
    (0x7ff0000000000000, 0x7ff0000000000000, true),
    (0xfff0000000000000, 0x7ff0000000000000, true),
    (0x7ff8000000000021, 0x7ff8000000000021, true),
    (0xfff0000000000001, 0x7ff0000000000001, true)]
  cases.all (fun (input, magnitude, flag) =>
    let args : Functions.Actual := ⟨[value input], []⟩
    decide (result (invoke .abs args {}) = .ok (value magnitude) ∧
      result (invoke .bool args {}) = .ok (.scalar (.bool flag)) ∧
      result (invoke .type args {}) = .ok (.string "float"))) = true

-- A host-supplied value reaches the same resolved call path through a first-class alias.
#guard
  let input : Binding := ⟨.local, "input"⟩
  let callee : Binding := ⟨.local, "magnitude"⟩
  let out : Binding := ⟨.local, "out"⟩
  let initial : State := { heap := #[⟨.list [], false⟩], iterators := [0] }
  let state := (initial.write input (value 0xfff0000000000000)).write callee (.builtin .abs)
  let args : Arguments := { positional := [.read (.bound input)] }
  let call := run #[] (.call (some out) (.read (.bound callee)) args) state
  let after := finishState call
  result call = .ok Flow.next ∧ after.bindingValue out = .ok (value 0x7ff0000000000000) ∧
    after.heap = state.heap ∧ after.iterators = state.iterators

-- Raw representation equality is distinct from Starlark comparison.
#guard
  let negZero := Value.float 0x8000000000000000
  let posZero := Value.float 0
  let posNaN := Value.float 0x7ff8000000000021
  let negNaN := Value.float 0xfff0000000000001
  negZero ≠ posZero ∧ posNaN ≠ negNaN ∧ Builtin.resolve "float" = none ∧
    applyBinary .eq negZero posZero = .ok (.bool true) ∧
    applyBinary .eq posNaN negNaN = .ok (.bool true) ∧
    applyBinary .add negZero posZero = .error (.binaryType .add)

private def compareInBody (op : BinaryOp) (lhs rhs : Value) : Except Failure Value :=
  runFunctionBody [] [("x", lhs), ("y", rhs)] (.ret (some (.binary op (.read "x") (.read "y"))))

private def checksOrder (lhs rhs : Value) (order : Ordering) : Bool :=
  let results : List (BinaryOp × Bool) := [(.eq, order == .eq), (.ne, order != .eq),
    (.lt, order == .lt), (.le, order != .gt), (.gt, order == .gt), (.ge, order != .lt)]
  results.all fun (op, expected) => decide (compareInBody op lhs rhs = .ok (.bool expected))

#guard
  let negZero := Value.float 0x8000000000000000
  let posInf := Value.float 0x7ff0000000000000
  let negInf := Value.float 0xfff0000000000000
  let posNaN := Value.float 0x7ff8000000000021
  let negNaN := Value.float 0xfff0000000000001
  let boundary := Value.float 0x4340000000000000
  let boundaryInt := Int.shiftLeft 1 53
  let huge := Int.shiftLeft 1 1100
  let cases : List (Value × Value × Ordering) := [
    (negZero, .float 0, .eq), (negZero, .int 0, .eq),
    (.float 0x8000000000000001, negZero, .lt), (.float 1, .int 0, .gt),
    (.float 0x000fffffffffffff, .float 0x0010000000000000, .lt),
    (.int 1, .float 0x3ff8000000000000, .lt), (.int 2, .float 0x3ff8000000000000, .gt),
    (.float 0xbff8000000000000, .int (-1), .lt),
    (.int boundaryInt, boundary, .eq), (.int (boundaryInt + 1), boundary, .gt),
    (.int (boundaryInt + 1), .float 0x4340000000000001, .lt),
    (.int (-boundaryInt - 1), .float 0xc340000000000000, .lt),
    (.float 0x7fefffffffffffff, .int (Int.shiftLeft 1 1024), .lt),
    (.int huge, posInf, .lt), (.int (-huge), negInf, .gt),
    (negInf, posInf, .lt), (posInf, posInf, .eq),
    (posNaN, negNaN, .eq), (posNaN, posInf, .gt), (.int huge, negNaN, .lt),
    (.bool false, .bool true, .lt)]
  cases.all (fun (lhs, rhs, order) => checksOrder lhs rhs order && checksOrder rhs lhs order.swap) = true

#guard
  let cases : List (Value × Value) := [(.bool true, .int 1), (.bool false, .float 0),
    (.float 0x3ff0000000000000, .bool true), (.float 0x7ff8000000000001, .none)]
  cases.all (fun (lhs, rhs) => decide (compareInBody .eq lhs rhs = .ok (.bool false) ∧
    compareInBody .ne rhs lhs = .ok (.bool true) ∧
    compareInBody .lt lhs rhs = .error (.dynamic (.binaryType .lt)) ∧
    compareInBody .ge rhs lhs = .error (.dynamic (.binaryType .ge)))) = true ∧
  compareInBody .eq .none .none = .ok (.bool true) ∧
  compareInBody .lt .none .none = .error (.dynamic (.binaryType .lt))

#guard
  let lhs : Binding := ⟨.local, "x"⟩
  let rhs : Binding := ⟨.local, "y"⟩
  let frame : Frame := {}
  denoteExpr (.binary .eq (.read (.bound lhs)) (.read (.bound rhs))) frame =
      .error (.uninitialized lhs) ∧
    denoteExpr (.binary .lt (.read (.predeclared (.float 0))) (.read (.bound rhs))) frame =
      .error (.uninitialized rhs)

-- Float dictionary keys fail during display, read, or write. A tuple cannot hide the float.
#guard
  let rejects := fun (state : State) (key : Lists.Value) =>
    let display := Lists.addDisplayEntry [] key (.scalar .none) state
    let get := Lists.readIndex (.dict 0) key state
    let put := Lists.writeIndex (.dict 0) key (.scalar .none) state
    decide (result display = .error (.unhashableKey key) ∧
      result get = .error (.unhashableKey key) ∧ result put = .error (.unhashableKey key) ∧
      (finishState put).heap = state.heap)
  let key := value 0x3ff0000000000000
  let state : State := { heap := #[⟨.dict [], false⟩] }
  let tuple := Lists.allocateTuple [key] state
  let nested := Outcome.resume tuple (fun inner => Lists.allocateTuple [inner])
  let withList := finishState (Outcome.resume nested (fun outer => Lists.allocate [outer]))
  rejects state key && rejects withList (.tuple 1) &&
    rejects withList (.tuple 2) && rejects withList (.list 3)

-- Raw heap clients use the same restricted key code type for cached tuples and dictionary entries.
example : True := by
  fail_if_success have _ : Lists.KeyPart := .scalar (Value.float 0)
  trivial

end Silmaril.Languages.Starlark.Binary64
