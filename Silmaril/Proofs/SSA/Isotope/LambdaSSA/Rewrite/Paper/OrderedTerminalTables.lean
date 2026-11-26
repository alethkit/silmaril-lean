module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native recovery of ordered truth-table quotations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedTerminalTables

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open Paper.WithCaseBind.OpenReplay
open OrderedTables
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

theorem frame_eq {X : Ty Empty} (frame other : ReplyFrame X) : frame = other := by
  induction frame with
  | base => cases other; rfl
  | unit frame ih => cases other; congr 1; exact ih _
  | bit frame ih => cases other; congr 1; exact ih _

theorem bindSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) (distinct : Function.Injective slots) :
    Function.Injective (ReplyFrame.bindSlots slots) := by
  intro i j eq
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · cases eq
  · cases eq
  · exact congrArg Fin.succ (distinct (ReplyFrame.Slot.retainBit.inj eq))

theorem guardSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (distinct : Function.Injective slots) (test : Fin (n + 1)) :
    Function.Injective (ReplyFrame.guardSlots slots test) :=
  bindSlots_injective _ (fun _ _ eq =>
    Fin.succAbove_right_injective (distinct (ReplyFrame.Slot.retainUnit.inj eq)))

theorem standardSlots_injective : ∀ n, Function.Injective (ReplyFrame.standardSlots n)
  | 0 => fun i => i.elim0
  | n + 1 => bindSlots_injective _ (standardSlots_injective n)

private theorem locate_eq {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (kept : Fin n → ReplyFrame.Slot frame) (slot : ReplyFrame.Slot frame) (i : Fin n)
    (found : locate kept slot = some i) : kept i = slot := by
  unfold locate at found
  have hit := List.find?_some found
  let := ReplyFrame.Slot.decEq frame
  exact of_decide_eq_true hit

private theorem reindex_rows {X : Ty Empty} {frame : ReplyFrame X} {Γ : List (Ty Empty)} {n m : Nat}
    (e : Finite.Expr m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (table : Finite.Table n)
    (found : reindex? kept e slots = some table) (v : ReplyFrame.Value Γ frame) :
    e.eval (fun j => ((slots j).read v).1) = table (fun j => ((kept j).read v).1) := by
  induction e generalizing table with
  | literal bit =>
    simp only [reindex?, Option.some.injEq] at found
    subst table
    rfl
  | read i =>
    simp only [reindex?, Option.map_eq_some_iff] at found
    obtain ⟨j, located, rfl⟩ := found
    simp only [Finite.Expr.eval, locate_eq kept (slots i) j located]
  | split low high hl hr =>
    by_cases redundant : low = high
    · have reduced : reindex? kept low (fun j => slots j.succ) = some table := by
        simpa only [reindex?, redundant, ↓reduceIte] using found
      rw [← redundant]
      simpa [Finite.Expr.eval] using! hl _ _ reduced
    · simp only [reindex?, redundant, ↓reduceIte, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
        at found
      obtain ⟨j, located, l, left, r, right, rfl⟩ := found
      have same := congrArg (fun slot : ReplyFrame.Slot frame => (slot.read v).1)
        (locate_eq kept (slots 0) j located)
      simp only [Finite.Expr.eval, ← same]
      split
      · exact hr _ _ right
      · exact hl _ _ left

private theorem render_emits {L : List (Ty Empty)} {n : Nat} (emits before : List Bool)
    (p : Finite.Normal L n) :
    renderWith (emits.foldr Finite.Normal.emit p) before = renderWith p (before ++ emits) := by
  induction emits generalizing before with
  | nil => simp
  | cons b bs ih => simp [renderWith, ih, List.append_assoc]

theorem render_normal {L : List (Ty Empty)} {n : Nat} (p : Finite.Normal L n) (emits : List Bool) :
    (renderWith p emits).witnessed.normal = emits.foldr Finite.Normal.emit p := by
  induction p generalizing emits with
  | ret pos table =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil =>
      simp only [List.foldr_nil, Finite.Tree.normal]
      congr
      exact funext (Finite.Expr.quote_eval _ _)
    | cons b bs h => simp [Finite.Tree.normal, h]
  | emit bit next ih =>
    simp only [renderWith, ih, List.foldr_append, List.foldr_cons, List.foldr_nil]
  | request label l r hl hr =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil => simp [Finite.Tree.normal, hl, hr]
    | cons b bs h => simp [Finite.Tree.normal, h]
  | testRequest _ _ _ _ _ _ hfl hfr htl htr =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil => simp [Finite.Tree.normal, hfl, hfr, htl, htr]
    | cons b bs h => simp [Finite.Tree.normal, h]

set_option backward.isDefEq.respectTransparency false in
theorem recoverTree_sound {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (tree : ReadTree L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (normal : Finite.Normal L n)
    (found : recoverTree tree slots kept = some normal) :
    selectedEq (tree.selectedWith (fun j => (slots j).term))
      ((renderWith normal []).selectedWith (fun j => (kept j).term)) := by
  induction tree generalizing n X with
  | ret emits pos i =>
    simp only [recoverTree, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨j, located, rfl⟩ := found
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    apply CompactTerminal.selected_of_frame_rows
    intro Γ v
    rw [Finite.Expr.quote_eval]
    exact congrArg (fun slot : ReplyFrame.Slot frame => (slot.read v).1) (locate_eq kept (slots i) j located).symm
  | retExpr emits pos e =>
    simp only [recoverTree, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨table, reindexed, rfl⟩ := found
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    apply CompactTerminal.selected_of_frame_rows
    intro Γ v
    rw [Finite.Expr.quote_eval]
    exact reindex_rows e slots kept table reindexed v
  | request emits label bound l r hl hr =>
    simp only [recoverTree, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨left, hleft, right, hright, rfl⟩ := found
    have le := hl _ _ _ hleft
    have re := hr _ _ _ hright
    rw [bindSlots_term, bindSlots_term] at le re
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    exact case_congr _ le re
  | testRequest emits test low lowBound highBound fl fr tl tr hfl hfr htl htr =>
    cases n with
    | zero => simp [recoverTree] at found
    | succ n =>
      simp only [recoverTree, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      obtain ⟨i, located, fl', h₀, fr', h₁, tl', h₂, tr', h₃, rfl⟩ := found
      have flEq := hfl _ _ _ h₀
      have frEq := hfr _ _ _ h₁
      have tlEq := htl _ _ _ h₂
      have trEq := htr _ _ _ h₃
      rw [guardSlots_term, guardSlots_term] at flEq frEq tlEq trEq
      simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
      rw [locate_eq kept (slots test) i located]
      exact case_congr _ (case_congr _ flEq frEq) (case_congr _ tlEq trEq)

set_option backward.isDefEq.respectTransparency false in
theorem recoverSplit_sound {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (split : SelectedGuardSplit L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin (n + 1) → ReplyFrame.Slot frame) (normal : Finite.Normal L (n + 1))
    (found : recoverSplit split slots kept = some normal) :
    selectedEq (split.sourceWith (fun j => (slots j).term))
      ((renderWith normal []).selectedWith (fun j => (kept j).term)) := by
  rcases split with ⟨test, emits, fl, tl⟩
  cases fl <;> cases tl <;> try (solve | simp [recoverSplit, bind] at found)
  rename_i prefixF low boundF fl fr prefixT high boundT tl tr
  cases prefixF <;> cases prefixT <;> try (solve | simp [recoverSplit, bind] at found)
  by_cases labels : high = !low
  · subst high
    simp only [recoverSplit, bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
      ite_true] at found
    obtain ⟨i, located, fl', h₀, fr', h₁, tl', h₂, tr', h₃, rfl⟩ := found
    have flEq := recoverTree_sound _ _ _ _ h₀
    have frEq := recoverTree_sound _ _ _ _ h₁
    have tlEq := recoverTree_sound _ _ _ _ h₂
    have trEq := recoverTree_sound _ _ _ _ h₃
    rw [bindSlots_term, guardSlots_term] at flEq frEq tlEq trEq
    simp only [render_emits, List.nil_append, renderWith, SelectedGuardSplit.sourceWith, ReadTree.selectedWith]
    rw [locate_eq kept (slots test) i located]
    exact case_congr _ (case_congr _ flEq frEq) (case_congr _ tlEq trEq)
  · simp [recoverSplit, bind, labels] at found

private theorem reframed_slots_term {X : Ty Empty} {f f' : ReplyFrame X} {m : Nat} (same : f = f')
    (slots : Fin m → ReplyFrame.Slot f) :
    (fun i => ((same ▸ slots : Fin m → ReplyFrame.Slot f') i).term) = fun i => (slots i).term := by
  cases same
  rfl

theorem recovered_packed {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext (n + 1)) L)
    (frameEq : p.frame = ReplyFrame.standard (n + 1)) (key : Finite.Normal L (n + 1))
    (found : recoverSplit p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) = some key) :
    p.packedSource = (OrderedTables.target key).packed := by
  have replay := recoverSplit_sound p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) key found
  rw [reframed_slots_term frameEq p.slots, standardSlots_term] at replay
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (replay.lsubstPost p.source.elaborate.property (OrderedTables.target key).property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

theorem observations_eq {L : List (Ty Empty)} {n : Nat} {p : SelectedAt (replyContext n) L}
    (a : OrderedTables.Admission p) (env : Finite.Assignment n) :
    CanonicalLive.observations p env = a.key.outcomes env := by
  have map := CanonicalLive.readTree_map_outcomes (renderWith a.key []) env
  rw [render_normal, List.foldr_nil] at map
  exact (congrArg (fun arrow => ((CanonicalLive.payloadDenote.map arrow).of (replyInput n env)).outcomes)
    a.packed_eq).trans map

theorem key_eq_of_packed_eq {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : OrderedTables.Admission p) (r : OrderedTables.Admission q) (eq : p.packedSource = q.packedSource) :
    l.key = r.key := by
  apply Finite.Normal.traceTree_inj
  intro env
  apply Reply.Normal.outcomesWith_injective _ (Reply.Exits.Exit.packed_injective L)
  have same : CanonicalLive.observations p env = CanonicalLive.observations q env := by
    simp only [CanonicalLive.observations, eq]
  exact (observations_eq l env).symm.trans (same.trans (observations_eq r env))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedTerminalTables
