module

public import Silmaril.SSA.MLIR.Shape.Reduce.Defs

public section

namespace Silmaril.Proofs.MLIR.Shape.Reduce

open Silmaril.MLIR.Shape (ExtentTensor ReduceBody)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Pure (Eval OpSignature)

private theorem foldl_ofFn_zipIdx {α β : Type} {rank : Nat}
    (step : β → Nat → α → β) (extents : Fin rank → α) (start : Nat) (initial : β) :
    Fin.foldl rank (fun acc axis => step acc (start + axis.val) (extents axis)) initial =
      ((List.ofFn extents).zipIdx start).foldl (fun acc (extent, axis) => step acc axis extent) initial := by
  induction rank generalizing start initial with
  | zero => simp
  | succ rank ih =>
    rw [Fin.foldl_succ, List.ofFn_succ, List.zipIdx_cons, List.foldl_cons]
    have offset (axis : Fin rank) : start + axis.succ.val = (start + 1) + axis.val := by
      simp only [Fin.val_succ]
      omega
    simpa only [Fin.val_zero, Nat.add_zero, offset] using
      ih (fun axis => extents axis.succ) (start + 1) (step initial start (extents 0))

theorem denote_eq_foldl {Op : OpSignature} {indexWidth : Width} {Carried Captures : List Width}
    (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    body.denote evalOp shape initial captures =
      shape.toShape.zipIdx.foldl (fun carried (extent, axis) =>
        body.step evalOp (BitVec.ofNat indexWidth.val axis) (BitVec.ofNat indexWidth.val extent)
          carried captures) initial := by
  simpa only [ReduceBody.denote, ExtentTensor.toShape, Nat.zero_add] using
    foldl_ofFn_zipIdx (fun carried axis extent =>
      body.step evalOp (BitVec.ofNat indexWidth.val axis) (BitVec.ofNat indexWidth.val extent)
        carried captures) (fun axis => shape.2 (axis, ())) 0 initial

private theorem index_toInt {indexWidth : Width} {value : Nat}
    (fits : value < 2 ^ (indexWidth.val - 1)) :
    (BitVec.ofNat indexWidth.val value).toInt = (value : Int) := by
  have widthPositive := indexWidth.property
  have twice : 2 ^ indexWidth.val = 2 * 2 ^ (indexWidth.val - 1) := by
    calc
      2 ^ indexWidth.val = 2 ^ (indexWidth.val - 1 + 1) := by congr 1; omega
      _ = 2 * 2 ^ (indexWidth.val - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have unsignedExact : (BitVec.ofNat indexWidth.val value).toNat = value := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [twice]; omega)]
  have signedExact : 2 * (BitVec.ofNat indexWidth.val value).toNat < 2 ^ indexWidth.val := by
    rw [unsignedExact, twice]
    omega
  rw [BitVec.toInt_eq_toNat_of_lt signedExact, unsignedExact]

theorem step_indices_exact {shape : ExtentTensor} {indexWidth : Width}
    (fits : shape.ReduceFits indexWidth) (axis : Fin shape.1) :
    (BitVec.ofNat indexWidth.val axis.val).toInt = (axis.val : Int) ∧
      (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))).toInt = (shape.2 (axis, ()) : Int) :=
  ⟨index_toInt (Nat.lt_trans axis.isLt fits.1), index_toInt (fits.2 axis)⟩

theorem run?_of_rank_zero {Op : OpSignature} {indexWidth : Width} {Carried Captures : List Width}
    (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (rankZero : shape.1 = 0) : body.run? evalOp shape initial captures = some initial := by
  rcases shape with ⟨rank, extents⟩
  change rank = 0 at rankZero
  subst rank
  have fits : ExtentTensor.ReduceFits ⟨0, extents⟩ indexWidth :=
    ⟨Nat.two_pow_pos _, fun axis => axis.elim0⟩
  rw [ReduceBody.run?, ite_eq_left fits]
  rfl

end Silmaril.Proofs.MLIR.Shape.Reduce
