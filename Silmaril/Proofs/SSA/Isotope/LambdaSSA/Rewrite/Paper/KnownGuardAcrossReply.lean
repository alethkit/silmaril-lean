module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.AcrossReply.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native replay of a carried case fact through one request -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardAcrossReply

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed

theorem survives_succ {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame)
    (shift : p.afterTest = p.beforeTest.succ) : p.Survives slots := by
  unfold GuardAcrossReply.Survives
  rw [shift]
  rfl

private theorem guard_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty}
    (g : GuardRequest L (n + 2)) (test : Fin (n + 2))
    (slots : Fin (n + 2) → Term signature.Instr (product (product X unit) Bit) Bit)
    (b : Bool) : ValueBranches [product (product X unit) Bit] (g.prunedAfterReply test slots b) L :=
  prependEmits_typed g.emits (.let₁ (priorCaseUnit X).elaborate.property
    (applyPacked_typed_exits (g.live test slots b).elaborate.property))

private theorem request_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty}
    (r : RequestBeforeGuard L (n + 2)) (test : Fin (n + 2))
    (slots : Fin (n + 1) → Term signature.Instr (product X unit) Bit) (b : Bool) :
    ValueBranches [product X unit] (r.prunedWith test slots b) L :=
  .case (emitPrefix r.emits (.call (show signature.Instr from Op.ask r.label) .unit)).elaborate.property
    (applyPacked_typed_exits (guard_typed r.onLeft test (bindReply slots) b))
    (applyPacked_typed_exits (guard_typed r.onRight test (bindReply slots) b))

theorem pruned_typed {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} (p : GuardAcrossReply L n)
    (slots : Fin (n + 1) → Term signature.Instr X Bit) : ValueBranches [X] (p.prunedWith slots) L :=
  .case (emitPrefix p.emits (slots p.beforeTest)).elaborate.property
    (applyPacked_typed_exits (request_typed p.onFalse p.afterTest (fun j => retainSlot (slots j)) false))
    (applyPacked_typed_exits (request_typed p.onTrue p.afterTest (fun j => retainSlot (slots j)) true))

private theorem transported_term {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) (survives : p.Survives slots) :
    bindReply (fun j => retainSlot (A := unit) (slots j).term) p.afterTest =
      retainSlot (A := Bit) (retainSlot (A := unit) (slots p.beforeTest).term) := by
  have map_eq := congrFun (bindSlots_term (fun j => ReplyFrame.Slot.retainUnit (slots j))) p.afterTest
  exact map_eq.symm.trans (congrArg ReplyFrame.Slot.term survives)

set_option backward.isDefEq.respectTransparency false in
private theorem guard_at {Γ L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) (survives : p.Survives slots)
    (v : ReplyFrame.Value Γ frame) (g : GuardRequest L (n + 2)) :
    let slot := slots p.beforeTest
    let scope := bindReply (fun j => retainSlot (A := unit) (slots j).term)
    let packet := Tm.pair (.pair (v.elaborate.val.rename Nat.succ) ((slot.read v).2.val.rename Nat.succ)) (.var 0)
    E (Bit :: Γ) (((g.tree p.afterTest).selectedWith scope).elaborate.val.substVars (Tm.singleSubst packet))
      ((g.prunedAfterReply p.afterTest scope (slot.read v).1).substVars (Tm.singleSubst packet)) L := by
  let slot := slots p.beforeTest
  let scope := bindReply (fun j => retainSlot (A := unit) (slots j).term)
  let left := (g.live p.afterTest scope false).elaborate
  let right := (g.live p.afterTest scope true).elaborate
  have eq := framed_case_afterReply_at slot g.emits v left.property right.property
  have projection : scope p.afterTest = retainSlot (A := Bit) (retainSlot (A := unit) slot.term) :=
    transported_term p slots survives
  rw [← projection] at eq
  let packet := Tm.pair (.pair (v.elaborate.val.rename Nat.succ)
    ((slot.read v).2.val.rename Nat.succ)) (.var 0)
  change E (Bit :: Γ)
    (((g.tree p.afterTest).selectedWith scope).elaborate.val.substVars (Tm.singleSubst packet))
    ((g.prunedAfterReply p.afterTest scope (slot.read v).1).substVars (Tm.singleSubst packet)) L
  cases tag : (slot.read v).1
  · simp only [tag, Bool.false_eq_true, ↓reduceIte] at eq
    exact eq
  · simp only [tag, ↓reduceIte] at eq
    exact eq

set_option backward.isDefEq.respectTransparency false in
private theorem request_at {Γ L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) (survives : p.Survives slots)
    (v : ReplyFrame.Value Γ frame) (r : RequestBeforeGuard L (n + 2)) :
    let slot := slots p.beforeTest
    let retained := fun j => retainSlot (A := unit) (slots j).term
    let packet := Tm.pair v.elaborate.val (slot.read v).2.val
    E Γ (((r.tree p.afterTest).selectedWith retained).elaborate.val.substVars (Tm.singleSubst packet))
      ((r.prunedWith p.afterTest retained (slot.read v).1).substVars (Tm.singleSubst packet)) L := by
  let slot := slots p.beforeTest
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let scope := bindReply retained
  let oldLeft := ((r.onLeft.tree p.afterTest).selectedWith scope).elaborate
  let oldRight := ((r.onRight.tree p.afterTest).selectedWith scope).elaborate
  let newLeft := guard_typed r.onLeft p.afterTest scope (slot.read v).1
  let newRight := guard_typed r.onRight p.afterTest scope (slot.read v).1
  exact packed_case_congr_at
    (emitPrefix r.emits (.call (show signature.Instr from Op.ask r.label) .unit))
    (.pair v.elaborate.property (slot.read v).2.property)
    oldLeft.property oldRight.property newLeft newRight
    (guard_at p slots survives v r.onLeft) (guard_at p slots survives v r.onRight)

set_option backward.isDefEq.respectTransparency false in
theorem eq_pruned {L : List (Ty Empty)} {n : Nat} {X : Ty Empty} {frame : ReplyFrame X}
    (p : GuardAcrossReply L n) (slots : Fin (n + 1) → ReplyFrame.Slot frame) (survives : p.Survives slots) :
    E [X] (p.sourceWith (fun j => (slots j).term)).elaborate.val
      (p.prunedWith (fun j => (slots j).term)) L := by
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let oldFalse := ((p.onFalse.tree p.afterTest).selectedWith retained).elaborate
  let oldTrue := ((p.onTrue.tree p.afterTest).selectedWith retained).elaborate
  let newFalse := request_typed p.onFalse p.afterTest retained false
  let newTrue := request_typed p.onTrue p.afterTest retained true
  apply frame_case_ext frame (p.sourceWith _).elaborate.property.hasType (pruned_typed p _).hasType
  intro Γ v
  have source := framed_case_at (slots p.beforeTest) p.emits v oldFalse.property oldTrue.property
  have target := framed_case_at (slots p.beforeTest) p.emits v newFalse newTrue
  refine source.trans ((prependEmits_congr p.emits ?_).trans target.symm)
  cases tag : ((slots p.beforeTest).read v).1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [tag] using request_at p slots survives v p.onFalse
  · simp only [↓reduceIte]
    simpa only [tag] using request_at p slots survives v p.onTrue

theorem packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : GuardAcrossReply L n)
    (survives : p.Survives (ReplyFrame.standardSlots (n + 1))) :
    p.packedSource =
      Paper.Extension.Singleton.ofRegion Seed (pruned_typed p (readReply (n + 1))).packExits := by
  have native := eq_pruned p (ReplyFrame.standardSlots (n + 1)) survives
  rw [standardSlots_term] at native
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (native.lsubstPost (p.sourceWith (readReply (n + 1))).elaborate.property
      (pruned_typed p (readReply (n + 1))) (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardAcrossReply
