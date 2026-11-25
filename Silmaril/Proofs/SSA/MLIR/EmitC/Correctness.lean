module

public import Silmaril.SSA.MLIR.EmitC.Defs

public section

namespace Silmaril.Proofs.MLIR.EmitC

open Silmaril.MLIR
open Silmaril.MLIR.EmitC

variable {Γ : List Arith.Width}

theorem eval_eq_ok_iff (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ) (result : Int) :
    add.eval abi env = .ok result ↔
      abi = .signedInt ∧ FitsInt32 (add.signedSum env) ∧ add.signedSum env = result := by
  simp only [Add.eval]
  split <;> rename_i admitted
  · split <;> rename_i fits
    · rw [Except.ok.injEq, and_iff_right admitted, and_iff_right fits]
    · constructor
      · intro h
        cases h
      · intro h
        exact (fits h.2.1).elim
  · simp [admitted]

theorem toArith_denote_of_eval (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ)
    (result : Int) (defined : add.eval abi env = .ok result) :
    add.toArith.denote env = BitVec.ofInt 32 result := by
  have ⟨_, _, sumEq⟩ := (eval_eq_ok_iff add abi env result).mp defined
  rw [← sumEq]
  change env.get add.lhs + env.get add.rhs =
    BitVec.ofInt 32 ((env.get add.lhs).toInt + (env.get add.rhs).toInt)
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]

theorem toArith_signed_of_eval (add : Add Γ) (abi : Int32ABI) (env : Arith.Env Γ)
    (result : Int) (defined : add.eval abi env = .ok result) :
    (add.toArith.denote env).toInt = result := by
  have ⟨_, fits, sumEq⟩ := (eval_eq_ok_iff add abi env result).mp defined
  have resultFits : FitsInt32 result := sumEq ▸ fits
  rw [toArith_denote_of_eval add abi env result defined]
  exact BitVec.toInt_ofInt_eq_self (by decide) resultFits.1 resultFits.2

end Silmaril.Proofs.MLIR.EmitC
