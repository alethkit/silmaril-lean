module

import Silmaril.Languages.Starlark.Binary64.Thms
import Silmaril.Languages.Starlark.Functions.Builtins.Thms
import Silmaril.Languages.Starlark.Functions.Thms
import Silmaril.Numeric.Ieee754
meta import Silmaril.Languages.Starlark.Functions.Builtins.Defs
meta import Silmaril.Languages.Starlark.Functions.Denotation.Defs
meta import Silmaril.Languages.Starlark.Lists.Defs

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
  let nan := Value.float 0x7ff8000000000021
  let ops : List BinaryOp := [.eq, .ne, .lt, .le, .gt, .ge, .add]
  negZero ≠ posZero ∧ Builtin.resolve "float" = none ∧
    ops.all (fun op => decide
      (applyBinary op negZero posZero = .error (.binaryType op) ∧
       applyBinary op nan nan = .error (.binaryType op) ∧
       applyBinary op negZero (.int 0) = .error (.binaryType op) ∧
       applyBinary op (.int 0) posZero = .error (.binaryType op))) = true

-- Float dictionary keys fail during display, read, or write. A tuple cannot hide the float.
#guard
  let key := value 0x3ff0000000000000
  let state : State := { heap := #[⟨.dict [], false⟩] }
  let display := Lists.addDisplayEntry [] key (.scalar .none) state
  let get := Lists.readIndex (.dict 0) key state
  let put := Lists.writeIndex (.dict 0) key (.scalar .none) state
  let tuple := Lists.allocateTuple [key] state
  let nested := Outcome.resume tuple (fun inner => Lists.allocateTuple [inner])
  result display = .error (.unhashableKey key) ∧
    result get = .error (.unhashableKey key) ∧
    result put = .error (.unhashableKey key) ∧ (finishState put).heap = state.heap ∧
    (finishState nested).keyOf (.tuple 1) = .error (.unhashableKey (.tuple 1)) ∧
    (finishState nested).keyOf (.tuple 2) = .error (.unhashableKey (.tuple 2))

end Silmaril.Languages.Starlark.Binary64
