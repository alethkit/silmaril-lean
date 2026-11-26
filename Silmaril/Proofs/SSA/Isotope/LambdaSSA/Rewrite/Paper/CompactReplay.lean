module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.CompactReplay.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.AdjacentSwap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ComputedTable.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native replay for compact terminals in independent slot orders -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

private theorem pack_selectedEq {L : List (Ty Empty)} {n : Nat}
    {l r : CaseTree signature.Instr (replyContext n) L} (h : selectedEq l r) :
    Paper.Extension.Singleton.ofRegion Seed l.elaborate.property.packExits =
      Paper.Extension.Singleton.ofRegion Seed r.elaborate.property.packExits :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (h.lsubstPost l.elaborate.property r.elaborate.property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

theorem orderedExpr_quote {L : List (Ty Empty)} {n : Nat} (e : OrderedExpr n)
    (emits : List Bool) (pos : Position L) :
    selectedEq (e.selected emits pos)
      (selectTerminal pos (Finite.Expr.quote n e.packetEval) (readReply n) emits) := by
  have recover : (fun row : Finite.Assignment n => e.packetEval (row ∘ e.order.symm)) = e.expr.eval := by
    funext row
    have eta : (row ∘ e.order.symm) ∘ e.order = row := by
      funext j
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact congrArg e.expr.eval eta
  have perm := selected_permute_quote pos emits e.packetEval e.order
  rw [recover] at perm
  exact (quote_eval_selected e.expr pos (readReply n ∘ e.order) emits
    (fun j => readReply_discards n (e.order j))).symm.trans perm.symm

private theorem agreed_packetEval {n : Nat} {e f : OrderedExpr n} (h : e.Agrees f) :
    e.packetEval = f.packetEval := by
  funext row
  have eta : ((row ∘ e.order) ∘ e.order.symm) ∘ f.order = row ∘ f.order := by
    funext j
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
  exact (h (row ∘ e.order)).trans (congrArg f.expr.eval eta)

theorem orderedExpr_eq {L : List (Ty Empty)} {n : Nat} (e f : OrderedExpr n)
    (emits : List Bool) (pos : Position L) (h : e.Agrees f) :
    selectedEq (e.selected emits pos) (f.selected emits pos) := by
  have rhs := orderedExpr_quote f emits pos
  rw [← agreed_packetEval h] at rhs
  exact (orderedExpr_quote e emits pos).trans rhs.symm

set_option backward.isDefEq.respectTransparency false in
theorem RequestSkeleton.selected_eq_quoted {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : selectedEq (s.selected leaves) (s.quoted leaves).selected := by
  induction s with
  | ret emits pos => exact orderedExpr_quote leaves emits pos
  | request emits label left right il ir =>
    exact NativeReplay.case_congr (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit))
      (il leaves.1) (ir leaves.2)

theorem RequestSkeleton.packed_eq_quoted {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (leaves : s.Leaves) : s.packed leaves = Paper.WithCaseBind.OpenReplay.packed (s.quoted leaves) :=
  pack_selectedEq (RequestSkeleton.selected_eq_quoted s leaves)

private theorem RequestSkeleton.quoted_congr {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (l r : s.Leaves) (h : s.Agrees l r) : s.quoted l = s.quoted r := by
  induction s with
  | @ret n emits pos =>
    exact congrArg (fun t => ReadTree.retExpr emits pos (Finite.Expr.quote n t)) (agreed_packetEval h)
  | request emits label left right il ir =>
    exact congrArg₂ (ReadTree.request emits label false) (il _ _ h.1) (ir _ _ h.2)

theorem RequestSkeleton.packed_eq {L : List (Ty Empty)} {n : Nat} (s : RequestSkeleton L n)
    (l r : s.Leaves) (h : s.Agrees l r) : s.packed l = s.packed r :=
  (RequestSkeleton.packed_eq_quoted s l).trans
    ((congrArg Paper.WithCaseBind.OpenReplay.packed (RequestSkeleton.quoted_congr s l r h)).trans
      (RequestSkeleton.packed_eq_quoted s r).symm)

def RequestOnly.present {L : List (Ty Empty)} :
    {n : Nat} → {p : ReadTree L n} → RequestOnly p → RequestPresentation p
  | n, _, .ret emits pos i => ⟨.ret emits pos, ⟨.read i, Equiv.refl (Fin n)⟩, rfl⟩
  | n, _, .retExpr emits pos e => ⟨.ret emits pos, ⟨e, Equiv.refl (Fin n)⟩, rfl⟩
  | _, _, .request emits label _ hl hr =>
    let l := present hl
    let r := present hr
    ⟨.request emits label l.skeleton r.skeleton, (l.leaves, r.leaves),
      congrArg₂ (selectRequest emits label) l.selected_eq r.selected_eq⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CompactReplay
