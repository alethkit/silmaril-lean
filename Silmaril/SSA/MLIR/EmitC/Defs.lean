module

public import Silmaril.SSA.MLIR.Arith.Defs

/-! # EmitC signed addition

One decoded `emitc.add` with signless `i32` operands and result, corresponding
to `int32_t z = x + y;` in C. Inputs are already evaluated scalar values.
-/

@[expose] public section

namespace Silmaril.MLIR.EmitC

/-- The caller supplies the target's `int32_t` typedef status. -/
inductive Int32ABI where
  /-- `int32_t` is a typedef for `signed int`. Both operands keep that type
  under integer promotion, and the addition and destination have the same type. -/
  | signedInt
  /-- Any other underlying type, or a target without `int32_t`. -/
  | unsupported
  deriving DecidableEq

inductive EvalError where
  | unsupportedABI
  | signedOverflow
  deriving DecidableEq

abbrev i32 : Arith.Width := ⟨32, by decide⟩

/-- An SSA addition of two references to already available `i32` values. -/
structure Add (Γ : List Arith.Width) where
  lhs : Arith.Var Γ i32
  rhs : Arith.Var Γ i32

/-- The value range of C's exact-width signed `int32_t`. -/
abbrev FitsInt32 (value : Int) : Prop :=
  -(2 ^ 31) ≤ value ∧ value < 2 ^ 31

/-- The mathematical sum under the signed interpretation of the input bits. -/
def Add.signedSum {Γ : List Arith.Width} (add : Add Γ) (env : Arith.Env Γ) : Int :=
  (env.get add.lhs).toInt + (env.get add.rhs).toInt

/-- On the admitted profile, a representable sum is the stored result.
An unrepresentable sum is C signed overflow. An unsupported typedef yields
an admission error before evaluating the operation. -/
def Add.eval {Γ : List Arith.Width} (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ) :
    Except EvalError Int :=
  if abi = .signedInt then
    let sum := add.signedSum env
    if FitsInt32 sum then .ok sum else .error .signedOverflow
  else .error .unsupportedABI

/-- Use one flag-free `arith.addi` and return its result. -/
def Add.toArith {Γ : List Arith.Width} (add : Add Γ) : Arith.Block Γ i32 :=
  .letOp (.binary .addi add.lhs add.rhs) (.yield .here)

end Silmaril.MLIR.EmitC
