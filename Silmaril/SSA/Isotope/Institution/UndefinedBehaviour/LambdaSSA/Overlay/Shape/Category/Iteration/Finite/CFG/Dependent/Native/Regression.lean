module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms
import Mathlib.Tactic.FinCases

/-! # Recognize a native packed cycle and check its actual entry -/

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax
  (Payload Primitives Reply emptyBindings Bindings.push model)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent
open Silmaril.Isotope.LambdaSSA.Region (packedExitType)

namespace LambdaSSAUBNativePackedRegression

private abbrev U : Silmaril.Ty Empty := .unit
private abbrev P : Silmaril.Ty Empty := .product U U
private abbrev Internal : List (Silmaril.Ty Empty) := [U, P]
private abbrev External : List (Silmaril.Ty Empty) := [U, U]
private abbrev Output : Silmaril.Ty Empty := .coprod (packedExitType External) (packedExitType Internal)
private abbrev State := Fin 6

private abbrev uval : Payload U := ⟨.unit, .unit⟩
private abbrev pval : Payload P := pairPayload uval uval

private theorem unit_payload (p : Payload U) : p = uval := by
  obtain ⟨_, h⟩ := p
  cases h
  rfl

private theorem product_payload (p : Payload P) : p = pval := by
  obtain ⟨_, h⟩ := p
  cases h with
  | pair a b => cases a; cases b; rfl

private def seeds : Fin 2 ≃ Packet Internal where
  toFun := Fin.cases ⟨0, uval⟩ (fun _ => ⟨1, pval⟩)
  invFun p := p.1
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro ⟨i, a⟩
    revert a
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      rw [unit_payload a]
      rfl
    · intro a
      obtain rfl := Fin.eq_zero j
      rw [product_payload a]
      rfl

private def exits : Fin 2 ≃ Packet External where
  toFun := Fin.cases ⟨0, uval⟩ (fun _ => ⟨1, uval⟩)
  invFun p := p.1
  left_inv i := by fin_cases i <;> rfl
  right_inv := by
    rintro ⟨i, a⟩
    revert a
    refine Fin.cases ?_ (fun j => ?_) i
    · intro a
      rw [unit_payload a]
      rfl
    · intro a
      obtain rfl := Fin.eq_zero j
      rw [unit_payload a]
      rfl

private def codes : Codes U Internal External 1 2 2 := ⟨fun _ => uval, seeds, exits⟩

private inductive Instr where
  | unitBlock
  | productBlock
  deriving DecidableEq

local instance : HasTy Instr (Silmaril.Ty Empty) :=
  ⟨fun f => match f with | .unitBlock => U | .productBlock => P, fun _ => Output⟩

private def replyJump (p : Packet Internal) (s : State) : Reply Output 6 :=
  let a := pack p
  .ret ⟨.inr a.val, .inr a.property⟩ s

private def replyExit (p : Packet External) (s : State) : Reply Output 6 :=
  let a := pack p
  .ret ⟨.inl a.val, .inl a.property⟩ s

private def primitive : Primitives Instr 6
  | .unitBlock, _, s =>
    match s.val with
    | 0 => replyJump ⟨1, pval⟩ 1
    | 3 => replyJump ⟨1, pval⟩ 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit ⟨0, uval⟩ s
  | .productBlock, _, s =>
    match s.val with
    | 1 => replyJump ⟨0, uval⟩ 2
    | 3 => replyJump ⟨0, uval⟩ 3
    | 4 => .fault 5
    | 5 => .diverge
    | _ => replyExit ⟨1, uval⟩ 2

/-- This source is written in the native syntax, including the local link. -/
private def producer (f : Instr) : Native.Typed Instr [instrSrc f, U] [Output] :=
  ⟨.cfg (.br 0 (.op f (.var 0))) 1 (fun _ => .br 1 (.var 0)),
    .cfg (fun _ : Fin 1 => Output)
      (.br (ℓ := 0) rfl (.op (f := f) (.var (i := 0) rfl)))
      (fun _ => .br (ℓ := 1) rfl (.var (i := 0) rfl))⟩

private def modifiedRoute {Γ : List (Silmaril.Ty Empty)} :
    Native.Typed Instr (Output :: Γ) (Internal ++ External) :=
  let k := Native.route Internal External (Γ := Γ) (Φ := Instr)
  ⟨.let₁ .unit (k.val.renameVars Nat.succ),
    .let₁ .unit (k.property.renameVars (LambdaSSA.Ren.wk (Output :: Γ) U))⟩

private def block (f : Instr) (modified : Bool) :
    Native.Typed Instr [instrSrc f, U] (Internal ++ External) :=
  Native.bind (producer f) (if modified then modifiedRoute else Native.route Internal External)

private def fixture (productEntry modified : Bool) : Native.Typed Instr [U] External :=
  let entry : Native.Typed Instr [U] (Internal ++ External) :=
    if productEntry then ⟨.br 1 (.pair .unit .unit), .br (ℓ := 1) rfl (.pair .unit .unit)⟩
    else ⟨.br 0 .unit, .br (ℓ := 0) rfl .unit⟩
  let blocks (j : Fin Internal.length) : Native.Typed Instr [Internal.get j, U] (Internal ++ External) :=
    Fin.cases (motive := fun i => Native.Typed Instr [Internal.get i, U] (Internal ++ External))
      (block .unitBlock modified)
      (Fin.cases (motive := fun i : Fin 1 => Native.Typed Instr [Internal.get i.succ, U] (Internal ++ External))
        (block .productBlock false) (fun i => i.elim0)) j
  ⟨nativeFeedback entry blocks, nativeFeedback_hasType entry blocks⟩

private abbrev source := fixture false false
private abbrev target := fixture true false
private abbrev changedRouter := fixture false true

private def readSource : Native.Readback Instr U Internal External :=
  (Native.recognize Internal source).get (by decide)

private def readTarget : Native.Readback Instr U Internal External :=
  (Native.recognize Internal target).get (by decide)

private theorem recognizes_source : Native.recognize Internal source = some readSource := rfl
private theorem recognizes_target : Native.recognize Internal target = some readTarget := rfl

private theorem rejects_changed_router : Native.recognize Internal changedRouter = none := rfl

private theorem proposed_before_router_check :
    Native.propose (X := U) Internal External changedRouter.val = some readSource := rfl

private abbrev code (p : Packet Internal) (s : State) := codes.invocation.symm (p, s)
private abbrev table := readSource.blocks.generate codes primitive
private abbrev env := emptyBindings.push uval

private theorem cross_typed_backedge :
    table 0 (code ⟨0, uval⟩ 0) = .repeat (code ⟨1, pval⟩ 1) ∧
    table 0 (code ⟨1, pval⟩ 1) = .repeat (code ⟨0, uval⟩ 2) :=
  ⟨rfl, rfl⟩

private noncomputable abbrev observed (raw : Native.Typed Instr [U] External) (s : State) :=
  Shape.denote (.native raw) (model primitive env) s

private theorem exit_after_backedge :
    observed source 0 = WithTop.some {Outcome.ret 0 .unit (2 : State)} :=
  (Native.classify_recognized recognizes_source codes primitive 0 0).trans rfl

private theorem distinct_entry_exit :
    observed target 0 = WithTop.some {Outcome.ret 1 .unit (2 : State)} :=
  (Native.classify_recognized recognizes_target codes primitive 0 0).trans rfl

private theorem silent_replay :
    observed source 3 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_recognized recognizes_source codes primitive 0 3).trans rfl

private theorem fault_state : observed source 4 = WithTop.some {Outcome.fault (5 : State)} :=
  (Native.classify_recognized recognizes_source codes primitive 0 4).trans rfl

private theorem in_step_divergence :
    observed source 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 2 Unit State)) :=
  (Native.classify_recognized recognizes_source codes primitive 0 5).trans rfl

private theorem rejects_distinct_native_entry :
    Native.check readSource readTarget codes primitive = false := by decide

private theorem rejected_refinement : ¬ ∀ s, observed source s ≤ observed target s := by
  intro ordered
  have checked := (Native.check_recognized_iff recognizes_source recognizes_target codes primitive).mpr
    (fun _ s => ordered s)
  rw [rejects_distinct_native_entry] at checked
  cases checked

#print axioms Native.recognized_eq
#print axioms Native.readback_agrees
#print axioms Native.generated_native_row
#print axioms Native.classify_recognized
#print axioms Native.check_recognized_iff
#print axioms recognizes_source
#print axioms rejects_changed_router
#print axioms proposed_before_router_check
#print axioms cross_typed_backedge
#print axioms exit_after_backedge
#print axioms distinct_entry_exit
#print axioms silent_replay
#print axioms fault_state
#print axioms in_step_divergence
#print axioms rejected_refinement

end LambdaSSAUBNativePackedRegression
