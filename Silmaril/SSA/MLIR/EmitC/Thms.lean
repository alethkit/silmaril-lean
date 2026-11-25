module

public import Silmaril.SSA.MLIR.EmitC.Defs
import Silmaril.Proofs.SSA.MLIR.EmitC.Correctness

public section

namespace Silmaril.MLIR.EmitC

variable {Γ : List Arith.Width}

/-- Evaluation succeeds exactly on the admitted ABI with a representable sum. -/
theorem Add.eval_eq_ok_iff (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ) (result : Int) :
    add.eval abi env = .ok result ↔
      abi = .signedInt ∧ FitsInt32 (add.signedSum env) ∧ add.signedSum env = result :=
  Proofs.MLIR.EmitC.eval_eq_ok_iff add abi env result

/-- The lowered block returns the encoding of the defined C result. -/
theorem Add.toArith_denote_of_eval (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ)
    (result : Int) (defined : add.eval abi env = .ok result) :
    add.toArith.denote env = BitVec.ofInt 32 result :=
  Proofs.MLIR.EmitC.toArith_denote_of_eval add abi env result defined

/-- Observing the lowered result as a signed integer recovers the defined C result. -/
theorem Add.toArith_signed_of_eval (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ)
    (result : Int) (defined : add.eval abi env = .ok result) :
    (add.toArith.denote env).toInt = result :=
  Proofs.MLIR.EmitC.toArith_signed_of_eval add abi env result defined

end Silmaril.MLIR.EmitC
