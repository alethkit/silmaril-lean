module

public import Silmaril.SSA.MLIR.Shape.Reduce.SCF.Defs

public section

namespace Silmaril.Proofs.MLIR.Shape.Reduce.SCF

open Silmaril.MLIR.Shape
open Silmaril.MLIR.Shape.ReduceBody
open Silmaril.MLIR.Arith (Width Var Env)
open Silmaril.MLIR.Pure (Code Eval Operands OpSignature)
open Silmaril.MLIR.SCF (For Yield Return)

variable {Op : OpSignature} {indexWidth : Width} {Carried Captures Γ Δ : List Width}

theorem extentTable_lookup (shape : ExtentTensor) (indexWidth : Width) (axis : Nat) :
    (extentTable indexWidth shape)[axis]? = if h : axis < shape.1 then
      some (BitVec.ofNat indexWidth.val (shape.2 (⟨axis, h⟩, ()))) else none := by
  rw [extentTable, Array.getElem?_ofFn]

private theorem toNat_index {value : Nat} (fits : value < 2 ^ (indexWidth.val - 1)) :
    (BitVec.ofNat indexWidth.val value).toNat = value := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le fits
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)))

theorem extentTable_lookup_of_axis {shape : ExtentTensor} (fits : shape.ReduceFits indexWidth)
    (axis : Fin shape.1) :
    (extentTable indexWidth shape)[(BitVec.ofNat indexWidth.val axis.val).toNat]? =
      some (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))) := by
  rw [toNat_index (Nat.lt_trans axis.isLt fits.1), extentTable_lookup, dite_eq_left axis.isLt]

private theorem get_weakenVar {w : Width} (args : Env Δ) (input : Env Γ) (ref : Var Γ w) :
    (args.append input).get (For.weakenVar ref Δ) = input.get ref := by
  induction args with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem get_liftRename {Locals : List Width} (locals : Env Locals)
    (rename : ∀ {w}, Var Γ w → Var Δ w) (source : Env Γ) (target : Env Δ)
    (agrees : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    {w : Width} (ref : Var (Locals ++ Γ) w) :
    (locals.append target).get (liftRename rename Locals ref) = (locals.append source).get ref := by
  induction locals with
  | nil => exact agrees ref
  | cons _ _ ih =>
    cases ref with
    | here => rfl
    | there ref => exact ih ref

private theorem eval_renameOperands (rename : ∀ {w}, Var Γ w → Var Δ w)
    (source : Env Γ) (target : Env Δ)
    (agrees : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (values : Operands Γ Carried) :
    (For.renameOperands rename values).eval target = values.eval source := by
  induction values with
  | nil => rfl
  | cons _ _ ih => simp only [For.renameOperands, Operands.eval, agrees, ih]

private theorem eval_argumentOperands (args : Env Carried) (input : Env Γ) :
    (For.argumentOperands Γ Carried).eval (args.append input) = args := by
  induction args with
  | nil => rfl
  | cons value rest ih =>
    simp only [For.argumentOperands, Env.append, Operands.eval, Env.get]
    rw [eval_renameOperands Var.there (rest.append input) (.cons value (rest.append input))
      (fun _ => rfl), ih]

private theorem lowerCode_eval (code : Code Op (fun scope => Operands scope Carried) Γ)
    (evalOp : Eval Op) (rename : ∀ {w}, Var Γ w → Var Δ w) (source : Env Γ) (target : Env Δ)
    (agrees : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (lowerCode (indexWidth := indexWidth) code rename).eval (forEval evalOp) Yield.eval target =
      code.eval evalOp (fun values env => values.eval env) source := by
  induction code generalizing Δ with
  | terminator values => exact eval_renameOperands rename source target agrees values
  | letOp op args rest ih =>
    simp only [lowerCode, Code.eval, forEval, eval_renameOperands rename source target agrees]
    apply ih
    exact get_liftRename (.cons (evalOp op (args.eval source)) .nil) rename source target agrees

private theorem get_lowerBodyRef (shape : ExtentTensor) (initial carried : Env Carried)
    (captures : Env Captures) (axis extent : BitVec indexWidth.val) {w : Width}
    (ref : Var (indexWidth :: indexWidth :: (Carried ++ Captures)) w) :
    (Env.cons extent (.cons axis (carried.append (lowerInput shape initial captures)))).get
      (lowerBodyRef ref) = (Env.cons axis (.cons extent (carried.append captures))).get ref := by
  cases ref with
  | here => rfl
  | there ref =>
    cases ref with
    | here => rfl
    | there ref =>
      exact get_liftRename carried _ captures _
        (fun ref => get_weakenVar
          (.cons (0 : BitVec indexWidth.val) (.cons (BitVec.ofNat indexWidth.val shape.1)
            (.cons (1 : BitVec indexWidth.val) initial))) captures ref) ref

theorem lowerToFor_body_eval (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial carried : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) (axis : Fin shape.1) :
    (body.lowerToFor shape supported).body.eval (forEval evalOp) Yield.eval
        (.cons (BitVec.ofNat indexWidth.val axis.val) (carried.append (lowerInput shape initial captures))) =
      body.step evalOp (BitVec.ofNat indexWidth.val axis.val)
        (BitVec.ofNat indexWidth.val (shape.2 (axis, ()))) carried captures := by
  simp only [lowerToFor, Code.eval, forEval, Operands.eval, Env.get, extentTable_lookup_of_axis fits axis,
    Option.getD_some]
  exact lowerCode_eval body evalOp lowerBodyRef _ _ (get_lowerBodyRef shape initial carried captures _ _)

private theorem init_eval (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) :
    (body.lowerToFor shape supported).init.eval (lowerInput shape initial captures) = initial := by
  simp only [lowerToFor]
  rw [eval_renameOperands (fun v => .there (.there (.there v))) (initial.append captures)
    (lowerInput (indexWidth := indexWidth) shape initial captures) (fun _ => rfl), eval_argumentOperands]

private theorem inductionAt_eq (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (axis : Nat) :
    (body.lowerToFor shape supported).inductionAt (lowerInput shape initial captures) axis = axis := by
  change (0 : BitVec indexWidth.val).toNat + axis * (1 : BitVec indexWidth.val).toNat = axis
  simp [BitVec.toNat_one indexWidth.property]

theorem lowerToFor_tripCount (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).tripCount (lowerInput shape initial captures) = shape.1 := by
  change ((BitVec.ofNat indexWidth.val shape.1).toNat - (0 : BitVec indexWidth.val).toNat +
    ((1 : BitVec indexWidth.val).toNat - 1)) / (1 : BitVec indexWidth.val).toNat = shape.1
  simp [toNat_index fits.1, BitVec.toNat_one indexWidth.property]

theorem lowerToFor_admitted (body : ReduceBody Op indexWidth Carried Captures)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).Admitted (lowerInput shape initial captures) := by
  constructor
  · change 0 < (1 : BitVec indexWidth.val).toNat
    simp [BitVec.toNat_one indexWidth.property]
  · rw [inductionAt_eq, lowerToFor_tripCount body shape initial captures supported fits]
    exact Nat.lt_of_lt_of_le fits.1 (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))

private theorem denoteFrom_zero {Input Result : List Width} (loop : For Op Input Result)
    (evalOp : Eval Op) (input : Env Input) (axis : Nat) (carried : Env loop.Carried) :
    loop.denoteFrom evalOp input 0 axis carried = loop.cont.eval evalOp Return.eval (carried.append input) :=
  rfl

private theorem denoteFrom_succ {Input Result : List Width} (loop : For Op Input Result)
    (evalOp : Eval Op) (input : Env Input) (remaining axis : Nat) (carried : Env loop.Carried) :
    loop.denoteFrom evalOp input (remaining + 1) axis carried =
      loop.denoteFrom evalOp input remaining (axis + 1) (loop.body.eval evalOp Yield.eval
        (.cons (BitVec.ofNat loop.width.val (loop.inductionAt input axis)) (carried.append input))) :=
  rfl

private theorem denoteFrom_eq_foldl (body : ReduceBody Op indexWidth Carried Captures)
    (evalOp : Eval Op) (shape : ExtentTensor) (initial carried : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) (remaining axis : Nat)
    (endsAtRank : axis + remaining = shape.1) :
    (body.lowerToFor shape supported).denoteFrom (forEval evalOp) (lowerInput shape initial captures)
        remaining axis carried =
      Fin.foldl remaining (fun state i =>
        let atAxis : Fin shape.1 := ⟨axis + i.val, by omega⟩
        body.step evalOp (BitVec.ofNat indexWidth.val atAxis.val)
          (BitVec.ofNat indexWidth.val (shape.2 (atAxis, ()))) state captures) carried := by
  induction remaining generalizing axis carried with
  | zero =>
    exact (denoteFrom_zero (body.lowerToFor shape supported) (forEval evalOp)
      (lowerInput shape initial captures) axis carried).trans
      (eval_argumentOperands carried (lowerInput (indexWidth := indexWidth) shape initial captures))
  | succ remaining ih =>
    have inBounds : axis < shape.1 := by omega
    rw [denoteFrom_succ (body.lowerToFor shape supported) (forEval evalOp)
      (lowerInput shape initial captures) remaining axis carried, inductionAt_eq]
    refine (congrArg (fun next : Env Carried => (body.lowerToFor shape supported).denoteFrom
      (forEval evalOp) (lowerInput shape initial captures) remaining (axis + 1) next)
      (lowerToFor_body_eval body evalOp shape initial carried captures supported fits ⟨axis, inBounds⟩)).trans ?_
    rw [Fin.foldl_succ]
    simp only [Fin.val_zero, Nat.add_zero]
    refine (ih _ _ (by omega)).trans ?_
    congr 1
    funext state i
    have atAxis : (⟨axis + 1 + i.val, by omega⟩ : Fin shape.1) =
        ⟨axis + i.succ.val, by simp only [Fin.val_succ]; omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    exact congrArg (fun j : Fin shape.1 => body.step evalOp (BitVec.ofNat indexWidth.val j.val)
      (BitVec.ofNat indexWidth.val (shape.2 (j, ()))) state captures) atAxis

theorem lowerToFor_run (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures)
    (supported : indexWidth.val ≤ 2 ^ 24 - 1) (fits : shape.ReduceFits indexWidth) :
    (body.lowerToFor shape supported).run (forEval evalOp) (lowerInput shape initial captures) =
      body.run? evalOp shape initial captures := by
  rw [For.run, ite_eq_left (lowerToFor_admitted body shape initial captures supported fits),
    ReduceBody.run?, ite_eq_left fits, For.denote,
    lowerToFor_tripCount body shape initial captures supported fits, init_eval,
    ReduceBody.denote]
  simpa only [Nat.zero_add] using congrArg some
    (denoteFrom_eq_foldl body evalOp shape initial initial captures supported fits shape.1 0 (Nat.zero_add _))

theorem runLowered?_eq (body : ReduceBody Op indexWidth Carried Captures) (evalOp : Eval Op)
    (shape : ExtentTensor) (initial : Env Carried) (captures : Env Captures) :
    body.runLowered? evalOp shape initial captures =
      if indexWidth.val ≤ 2 ^ 24 - 1 then body.run? evalOp shape initial captures else none := by
  by_cases supported : indexWidth.val ≤ 2 ^ 24 - 1
  · rw [runLowered?, dite_eq_left supported, ite_eq_left supported]
    by_cases fits : shape.ReduceFits indexWidth
    · rw [ite_eq_left fits]
      exact lowerToFor_run body evalOp shape initial captures supported fits
    · rw [ite_eq_right fits, ReduceBody.run?, ite_eq_right fits]
  · rw [runLowered?, dite_eq_right supported, ite_eq_right supported]

end Silmaril.Proofs.MLIR.Shape.Reduce.SCF
