module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Defs

import Silmaril.Semantics.Elgot.Partition.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics (Env extend extend_zero extend_succ)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer term term_rename)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Expr PacketType PrimitiveSignature Slot)
open Silmaril.Elgot (iter liftPure partitionTransfer partitionStepByTarget iter_partition_target)
open Silmaril.Elgot.ITree (Tree diverge diverge_bind iterate_fixpoint iterate_uniformity)

universe u w
variable {E : Type w → Type w} {F : Type} {α : Type u}
  {Γ : List PacketType} {exits blocks captures count : Nat}
  {sig : PrimitiveSignature F} {packets : Fin blocks → PacketType} {outputs : Fin exits → PacketType}

theorem load_ambient (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat) :
    frame.load values env (frame.shift + i) = env i := by
  induction frame generalizing env i with
  | entry => simp [Frame.load, Frame.shift]
  | push ty prev ih =>
    simp only [Frame.load, Frame.shift, Nat.add_assoc]
    rw [ih, show 2 + i = (i + 1) + 1 by omega]
    rfl

theorem load_slot (frame : Frame Γ) (values : Values Γ α) (env : Env α) (i : Nat)
    (packet : env i = frame.pack values) {ty : PacketType} (slot : Slot Γ ty) :
    frame.load values env (frame.position i slot) = values slot := by
  induction frame generalizing env i with
  | entry =>
    cases slot with
    | here => exact packet
    | there old => cases old
  | push ty prev ih =>
    cases slot with
    | here =>
      simp only [Frame.position, Frame.load]
      rw [show prev.shift = prev.shift + 0 by simp, load_ambient]
      rfl
    | there old =>
      simp only [Frame.position, Frame.load]
      exact ih _ _ 1 rfl old

private theorem unpack_tree (instr : Primitive E F α) (frame : Frame Γ) (values : Values Γ α)
    (env : Env α) (i : Nat) (body : Region F) (packet : env i = frame.pack values) :
    region instr env (frame.unpack i body) = region instr (frame.load values env) body := by
  induction frame generalizing env i with
  | entry => rfl
  | push ty prev ih =>
    simp only [Frame.unpack, region, term, pure_bind, packet, Frame.pack, Frame.load]
    exact ih _ _ 1 rfl

private theorem operand_tree (instr : Primitive E F α) (layout : Positions Γ)
    (env : Env α) (values : Values Γ α) {ty : PacketType} (value : Expr Γ ty)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot) :
    term instr env (operand layout value) = pure (evalOperand values value) := by
  induction value with
  | var slot => simp only [operand, term, evalOperand, agree]
  | unit => rfl
  | pair left right hl hr => simp only [operand, term, evalOperand, hl, hr, pure_bind]

private theorem exit_transfer (blocks : Nat) (port : Fin exits) (value : Value α) :
    splitTransfer blocks (blocks + port.val, value) = .inl (port.val, value) := by
  simp [splitTransfer, show ¬ blocks + port.val < blocks by omega]

private theorem local_transfer (label : Fin blocks) (value : Value α) :
    splitTransfer blocks (label.val, value) = .inr (label, value) := by
  simp [splitTransfer, label.isLt]

private theorem bind_agrees {ty : PacketType} (layout : Positions Γ) (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot)
    (payload : Value α) {τ : PacketType} (slot : Slot (ty :: Γ) τ) :
    extend env payload (bindPosition layout slot) = bindReply values payload slot := by
  cases slot with
  | here => rfl
  | there old => exact agree old

/-- Restored slots agree before the tail. Each selected case extends that
agreement with its payload, so the literal leaf sees the same packet
operands at any nesting depth. -/
private theorem case_tree {newBlocks : Nat} {β : Type u}
    (instr : Primitive E F α) (old : Fin blocks → Fin newBlocks) (layout : Positions Γ)
    (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (layout slot) = values slot)
    (tail : CaseTail packets outputs Γ) (finish : (Transfer α ⊕ BlockInput α newBlocks) → Tree E β) :
    (region instr env (CaseTail.erase old layout tail) >>= fun out => finish (splitTransfer newBlocks out)) =
      (CaseTail.run values tail >>= fun out => finish (Sum.map id (fun state => (old state.1, state.2)) out)) := by
  induction tail generalizing env with
  | jump label packet =>
    rw [CaseTail.erase, region, bind_assoc, operand_tree instr layout env values packet agree, pure_bind]
    cases label with
    | inl target => simp only [Sum.elim_inl, pure_bind, local_transfer, CaseTail.run, Sum.map_inr]
    | inr port => simp only [Sum.elim_inr, pure_bind, exit_transfer, CaseTail.run, Sum.map_inl, id_eq]
  | case test left right ihLeft ihRight =>
    simp only [CaseTail.erase, region, operand_tree instr layout env values test agree, pure_bind, CaseTail.run]
    cases evalOperand values test with
    | inl payload => exact ihLeft (bindPosition layout) _ _ (bind_agrees layout env values agree payload)
    | inr payload => exact ihRight (bindPosition layout) _ _ (bind_agrees layout env values agree payload)
    | atom _ | unit | pair _ _ => simp only [diverge_bind]

private theorem finish_old {newBlocks : Nat} (inner : BlockInput α newBlocks → Bool)
    (old : Fin blocks → Fin newBlocks) (outside : ∀ i packet, inner (old i, packet) = false)
    (run : BlockInput α newBlocks → Tree E (Transfer α ⊕ BlockInput α newBlocks))
    (out : Transfer α ⊕ BlockInput α blocks) :
    Sum.elim pure run (partitionTransfer inner (Sum.map id (fun state => (old state.1, state.2)) out)) =
      pure (Sum.map id (fun state => (old state.1, state.2)) out) := by
  rcases out with result | ⟨label, packet⟩
  · rfl
  · simp only [Sum.map_inr, partitionTransfer, outside, Bool.false_eq_true, ite_false, Sum.elim_inl]

private theorem unsplit_step (instr : Primitive E F α) (row : Row sig packets outputs Γ)
    (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (position slot) = values slot) :
    (region instr env (row.erase) >>= fun out => pure (splitTransfer blocks out)) =
      row.run instr values := by
  induction row generalizing env with
  | exit port value =>
    simp only [Row.erase, region, operand_tree instr position env values value agree, pure_bind,
      exit_transfer, Row.run]
  | jump target value =>
    simp only [Row.erase, region, operand_tree instr position env values value agree, pure_bind,
      local_transfer, Row.run]
  | branch tail =>
    change (region instr env (CaseTail.erase id position tail) >>= fun out => pure (splitTransfer blocks out)) = _
    rw [case_tree instr id position env values agree tail pure]
    have identity (out : Transfer α ⊕ BlockInput α blocks) :
        Sum.map id (fun state => (id state.1, state.2)) out = out := by cases out <;> rfl
    simp only [Row.run, identity, bind_pure]
  | request op arg tail ih =>
    simp only [Row.erase, region, term, operand_tree instr position env values arg agree, pure_bind,
      bind_assoc, Row.run]
    apply bind_congr
    intro reply
    apply ih
    intro τ slot
    cases slot with
    | here => rfl
    | there old => exact agree old

private noncomputable def step (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (p : BlockInput α blocks) :
    Tree E (Transfer α ⊕ BlockInput α blocks) :=
  region instr (extend env p.2) (graph.block p.1).erase >>= fun out => pure (splitTransfer blocks out)

/-- Evaluate a prefix to its first old transfer. Only a successor in the
fresh suffix can recurse in this inner run. -/
private theorem follow {newBlocks : Nat}
    (instr : Primitive E F α) (env : Env α) (graph : FiniteCFG F newBlocks exits captures)
    (inner : BlockInput α newBlocks → Bool) (old : Fin blocks → Fin newBlocks)
    (oldOutside : ∀ i packet, inner (old i, packet) = false)
    (row : Row sig packets outputs Γ) (frame : Frame Γ) (values : Values Γ α)
    (labels : Fin (row.requests + 1) → Fin newBlocks)
    (freshInside : ∀ (i : Fin row.requests) packet, inner (labels i.succ, packet) = true)
    (rows : ∀ i, (graph.block (labels i)).erase = (row.cells old frame labels i).2) :
    iter (partitionStepByTarget (step instr env graph) inner) (labels 0, frame.pack values) =
      Sum.map id (fun state => (old state.1, state.2)) <$> row.run instr values := by
  induction row with
  | exit port value =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    simp only [region, operand_tree instr _ _ values value (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, exit_transfer, partitionTransfer, Sum.elim_inl, Row.run, Sum.map_inl, id_eq]
  | jump target value =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    simp only [region, operand_tree instr _ _ values value (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, local_transfer, partitionTransfer, oldOutside, Bool.false_eq_true, ite_false, Sum.elim_inl,
      Row.run, Sum.map_inr]
  | branch tail =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl,
      case_tree instr old (frame.position 0) _ values (load_slot frame values (extend env (frame.pack values)) 0 rfl) tail
        (fun out => Sum.elim pure (iter (partitionStepByTarget (step instr env graph) inner))
          (partitionTransfer inner out))]
    simp only [Row.run, finish_old inner old oldOutside]
  | request op arg tail ih =>
    rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env graph) inner)) (labels 0, frame.pack values)]
    simp only [partitionStepByTarget, step, rows 0, Row.cells, Fin.cases_zero, map_eq_pure_bind, bind_assoc, pure_bind]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    have saved : frame.load values (extend env (frame.pack values)) frame.shift = frame.pack values := by
      simpa only [Nat.add_zero, extend_zero] using
        load_ambient frame values (extend env (frame.pack values)) 0
    simp only [region, term, operand_tree instr _ _ values arg (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, bind_assoc, extend_succ, extend_zero, saved, local_transfer, partitionTransfer, Row.run]
    apply bind_congr
    intro reply
    erw [freshInside (0 : Fin (tail.requests + 1)) (.pair (frame.pack values) reply)]
    simp only [ite_true, Sum.elim_inr]
    exact ih (.push (sig.reply op) frame) (bindReply values reply) (labels ∘ Fin.succ)
      (fun i packet => freshInside i.succ packet) (fun i => by
        have equation := rows i.succ
        simp only [Row.cells] at equation
        erw [Fin.cases_succ] at equation
        exact equation)

variable {source : FiniteCFG F blocks exits captures}
  (s : Shape sig outputs packets source) (emitted : Emitted s)

theorem table_chain (i : Fin (s.row.requests + 1)) :
    s.table (chainLabel s.selected s.row.requests i) = s.chain i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Shape.table, chainLabel, oldLabel]
  · simp [Shape.table, chainLabel, freshLabel]

theorem table_old (i : Fin blocks) (other : i ≠ s.selected) :
    s.table (oldLabel s.row.requests i) =
      (packets i, (source.block i).erase.renameLabels (moveExit blocks s.row.requests)) := by
  simp [Shape.table, oldLabel, other]

private theorem first_packet {newBlocks : Nat} (row : Row sig packets outputs Γ) (frame : Frame Γ)
    (old : Fin blocks → Fin newBlocks) (labels : Fin (row.requests + 1) → Fin newBlocks) :
    (row.cells old frame labels 0).1 = frame.packet := by
  cases row <;> rfl

theorem old_packet (i : Fin blocks) : (s.table (oldLabel s.row.requests i)).1 = packets i := by
  by_cases selected : i = s.selected
  · subst i
    change (s.table (chainLabel s.selected s.row.requests 0)).1 = _
    rw [table_chain]
    exact first_packet _ _ _ _
  · rw [table_old s i selected]

private theorem entry_run (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (start : Fin blocks) (seed : LambdaSSA.Tm F)
    (entry : graph.entry.erase = .br start.val seed) :
    region instr env graph.erase =
      term instr env seed >>= fun packet => iter (step instr env graph) (start, packet) := by
  simp only [FiniteCFG.erase, region, entry, bind_assoc, pure_bind, local_transfer, Sum.elim_inr]
  rfl

/-- Run the same flat row with two continuations that agree on its
relocated labels. This includes malformed raw operands that diverge. -/
private theorem rename_transfer {n labels : Nat} {β : Type u}
    (instr : Primitive E F α) (env : Env α) (row : Flat F labels n)
    (rename : Nat → Nat) (before after : Transfer α → Tree E β)
    (agree : ∀ i value, after (rename i, value) = before (i, value)) :
    (region instr env (row.erase.renameLabels rename) >>= after) = (region instr env row.erase >>= before) := by
  induction row generalizing env with
  | br label arg => simp only [Flat.erase, Region.renameLabels, region, bind_assoc, pure_bind, agree]
  | let₁ arg body ih => simp only [Flat.erase, Region.renameLabels, region, bind_assoc, ih]
  | let₂ arg body ih =>
    simp only [Flat.erase, Region.renameLabels, region, bind_assoc]
    apply bind_congr
    intro value
    cases value <;> first
      | exact ih _
      | change (diverge >>= after) = (diverge >>= before); rw [diverge_bind, diverge_bind]
  | case arg left right hl hr =>
    simp only [Flat.erase, Region.renameLabels, region, bind_assoc]
    apply bind_congr
    intro value
    cases value <;> first
      | exact hl _
      | exact hr _
      | change (diverge >>= after) = (diverge >>= before); rw [diverge_bind, diverge_bind]

private def embed (count : Nat) (state : BlockInput α blocks) : BlockInput α (blocks + count) :=
  (oldLabel count state.1, state.2)

private theorem relocate_transfer (count label : Nat) (value : Value α) :
    splitTransfer (blocks + count) (moveExit blocks count label, value) =
      Sum.map id (embed count) (splitTransfer blocks (label, value)) := by
  by_cases internal : label < blocks
  · have moved : label < blocks + count := by omega
    simp [moveExit, splitTransfer, internal, moved, embed, oldLabel]
  · have moved : ¬ blocks + count + (label - blocks) < blocks + count := by omega
    simp [moveExit, splitTransfer, internal, moved]

private theorem relocated_step {n labels : Nat} (instr : Primitive E F α) (env : Env α)
    (row : Flat F labels n) (count : Nat) :
    (region instr env (row.erase.renameLabels (moveExit blocks count)) >>= fun out =>
      pure (splitTransfer (blocks + count) out)) =
    Sum.map id (embed count) <$> (region instr env row.erase >>= fun out =>
      pure (splitTransfer blocks out)) := by
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  apply rename_transfer
  intro label payload
  rw [relocate_transfer]

private theorem unchanged (instr : Primitive E F α) (env : Env α) (i : Fin blocks)
    (other : i ≠ s.selected) (packet : Value α) :
    step instr env emitted.code (embed s.row.requests (i, packet)) =
      Sum.map id (embed s.row.requests) <$> step instr env source (i, packet) := by
  unfold step
  change (region instr (extend env packet) (emitted.code.block (oldLabel s.row.requests i)).erase >>= _) = _
  rw [emitted.row_eq, table_old s i other]
  exact relocated_step instr (extend env packet) (source.block i) s.row.requests

theorem unchanged_step (instr : Primitive E F α) (env : Env α) (i : Fin blocks)
    (other : i ≠ s.selected) (packet : Value α) :
    blockStep instr emitted.code env (oldLabel s.row.requests i, packet) =
      Sum.map id (fun state => (oldLabel s.row.requests state.1, state.2)) <$>
        blockStep instr source env (i, packet) := by
  change blockStep instr emitted.code env (embed s.row.requests (i, packet)) =
    Sum.map id (embed s.row.requests) <$> blockStep instr source env (i, packet)
  simpa only [blockStep, transfer, map_eq_pure_bind, step] using unchanged s emitted instr env i other packet

private def inFresh (oldBlocks : Nat) (p : BlockInput α count) : Bool :=
  decide (oldBlocks ≤ p.1.val)

private theorem fresh_inside (i : Fin (s.row.requests)) (packet : Value α) :
    inFresh blocks (chainLabel s.selected s.row.requests i.succ, packet) = true := by
  simp [inFresh, chainLabel, freshLabel]

private theorem old_outside (count : Nat) (i : Fin blocks) (packet : Value α) :
    inFresh blocks (embed count (i, packet)) = false := by
  simp [inFresh, embed, oldLabel, Nat.not_le_of_lt i.isLt]

private theorem step_square (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    (Sum.map id (embed s.row.requests) <$> step instr env source p) =
      iter (partitionStepByTarget (step instr env emitted.code) (inFresh blocks)) (embed s.row.requests p) := by
  rcases p with ⟨i, packet⟩
  by_cases selected : i = s.selected
  · subst i
    let values : Values [packets s.selected] α := readSlots position (extend env packet)
    have original : step instr env source (s.selected, packet) = s.row.run instr values := by
      change (region instr (extend env packet) (source.block s.selected).erase >>= _) = _
      rw [s.row_eq, unsplit_step instr s.row (extend env packet) values (fun _ => rfl)]
    rw [original]
    exact (follow instr env emitted.code (inFresh blocks) (oldLabel s.row.requests)
      (old_outside s.row.requests) s.row (.entry (packets s.selected)) values (chainLabel s.selected s.row.requests)
      (fresh_inside s) (fun j => by rw [emitted.row_eq, table_chain s]; rfl)).symm
  · rw [congrFun (iterate_fixpoint (partitionStepByTarget (step instr env emitted.code) (inFresh blocks)))
      (embed s.row.requests (i, packet))]
    simp only [partitionStepByTarget, unchanged s emitted instr env i selected packet,
      map_eq_pure_bind, bind_assoc, pure_bind]
    apply bind_congr
    intro out
    exact (finish_old (inFresh blocks) (oldLabel s.row.requests) (old_outside s.row.requests) _ out).symm

private theorem old_run (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    iter (step instr env source) p = iter (step instr env emitted.code) (embed s.row.requests p) := by
  let phases := partitionStepByTarget (step instr env emitted.code) (inFresh blocks)
  have simulation := iterate_uniformity (step instr env source) (iter phases) (embed s.row.requests) (by
    funext state
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
    exact step_square s emitted instr env state)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind, phases, iter_partition_target] using
    congrFun simulation p

theorem preserves_run (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase := by
  rw [entry_run instr env source s.entry _ s.entry_eq,
    entry_run instr env emitted.code (oldLabel s.row.requests s.entry) _ (emitted.entry_eq.trans s.entry_eq)]
  exact bind_congr fun packet => old_run s emitted instr env (s.entry, packet)

private theorem relocated_old_run (graph : FiniteCFG F (blocks + count) exits captures)
    (rows : ∀ i : Fin blocks, (graph.block (oldLabel count i)).erase =
      (source.block i).erase.renameLabels (moveExit blocks count))
    (instr : Primitive E F α) (env : Env α) (p : BlockInput α blocks) :
    iter (step instr env source) p = iter (step instr env graph) (embed count p) := by
  have simulation := iterate_uniformity (step instr env source) (step instr env graph) (embed count) (by
    funext state
    rcases state with ⟨i, packet⟩
    simp only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind]
    change Sum.map id (embed count) <$> step instr env source (i, packet) =
      (region instr (extend env packet) (graph.block (oldLabel count i)).erase >>= fun out =>
        pure (splitTransfer (blocks + count) out))
    rw [rows]
    exact (relocated_step instr (extend env packet) (source.block i) count).symm)
  simpa only [Bind.kleisliRight, liftPure, Function.comp_apply, pure_bind] using congrFun simulation p

namespace BranchEntry

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.BranchEntry
open Silmaril.Isotope.Bridge.NamedFlat.Capture (packEnv)

private theorem packed_input_tree (instr : Primitive E F α) (env : Env α) (context : List PacketType) :
    term instr env (Region.packedInputValue context) = pure (packEnv context.length env) := by
  induction context generalizing env with
  | nil => rfl
  | cons ty rest ih =>
    have older : term instr env ((Region.packedInputValue rest).rename Nat.succ) =
        term instr (env ∘ Nat.succ) (Region.packedInputValue rest) :=
      term_rename instr _ (fun _ => rfl)
    simp only [Region.packedInputValue, term, older, ih, pure_bind, List.length_cons, packEnv]

variable {context : BoundCtx PacketType captures}


theorem materialized_run (m : Materialized context source) (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env m.code.erase := by
  rw [entry_run instr env m.code (Fin.last blocks) _ m.entry_eq,
    packed_input_tree instr env context.toList, BoundCtx.length_toList, pure_bind,
    congrFun (iterate_fixpoint (step instr env m.code)) (Fin.last blocks, packEnv captures env)]
  change (region instr env source.entry.erase >>= fun out =>
    Sum.elim pure (iter (step instr env source)) (splitTransfer blocks out)) =
    ((region instr (extend env (packEnv captures env)) (m.code.block (Fin.last blocks)).erase >>= fun out =>
      pure (splitTransfer (blocks + 1) out)) >>= Sum.elim pure (iter (step instr env m.code)))
  rw [m.dispatch_eq, Silmaril.Isotope.Bridge.NamedFlat.Capture.unpack_tree instr m.written context env env, m.written_eq]
  simp only [bind_assoc, pure_bind]
  symm
  apply rename_transfer
  intro index value
  rw [relocate_transfer]
  cases splitTransfer blocks (index, value) with
  | inl out => rfl
  | inr next => exact (relocated_old_run m.code m.row_eq instr env next).symm

theorem seed_from_entry {A : Type 1} {Events : Type → Type}
    (instr : Primitive Events F A) (env : Env A)
    (seed : Silmaril.SSA.LambdaRTL.Val (Fin captures))
    (term_eq : packetTerm seed = (Region.packedInputValue context.toList : LambdaSSA.Tm F)) :
    packetValue env seed = packEnv captures env := by
  apply (Silmaril.Elgot.ITree.ret_inj (E := Events)).mp
  change (pure _ : Tree Events _) = pure _
  rw [← packet_term_tree instr env, term_eq, packed_input_tree, BoundCtx.length_toList]

theorem compiled_seed {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = packEnv captures env :=
  seed_from_entry instr env _ (Region.br.inj (built.publicReadback.provenance.sourceEntry.symm.trans
    (built.split.emitted.entry_eq.trans built.prepared.emitted.entry_eq))).2

end BranchEntry

namespace EffectfulEntry

open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry

variable {context : BoundCtx PacketType captures} {Δ : List PacketType}

private theorem pack_scope (instr : Primitive E F α) (frame : Frame Γ) (layout : Positions Γ)
    (env : Env α) :
    term instr env (packScope frame layout) = pure (frame.pack (readSlots layout env)) := by
  induction frame with
  | entry => rfl
  | push ty prev ih =>
    simp only [packScope, term, ih, pure_bind, Frame.pack, readSlots]
    rfl

private theorem case_congr {β : Type u} (instr : Primitive E F α) (env : Env α)
    (test : LambdaSSA.Tm F) (left right left' right' : Region F)
    (finish finish' : Transfer α → Tree E β)
    (hl : ∀ value, (region instr (extend env value) left >>= finish) =
      (region instr (extend env value) left' >>= finish'))
    (hr : ∀ value, (region instr (extend env value) right >>= finish) =
      (region instr (extend env value) right' >>= finish')) :
    (region instr env (.case test left right) >>= finish) =
      (region instr env (.case test left' right') >>= finish') := by
  simp only [region, bind_assoc]
  apply bind_congr
  intro value
  cases value with
  | inl payload => exact hl payload
  | inr payload => exact hr payload
  | atom _ | unit | pair _ _ => simp only [diverge_bind]

private theorem outlined_entry (m : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (ambient : Env α) :
    region instr ambient source.erase = region instr ambient m.code.erase := by
  let oldFinish : (Transfer α ⊕ BlockInput α blocks) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr ambient source))
  let newFinish : (Transfer α ⊕ BlockInput α (blocks + 2)) → Tree E (Transfer α) :=
    Sum.elim pure (iter (step instr ambient m.code))
  have routes (out : Transfer α ⊕ BlockInput α blocks) :
      newFinish (Sum.map id (embed 2) out) = oldFinish out := by
    cases out with
    | inl r => rfl
    | inr state => exact (relocated_old_run m.code m.old_eq instr ambient state).symm
  have bypass {Γ : List PacketType} (tail : CaseTail packets outputs Γ) (env : Env α) :
      (region instr env (CaseTail.erase id position tail) >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr env (CaseTail.erase (oldLabel 2) position tail) >>=
        fun out => newFinish (splitTransfer (blocks + 2) out)) := by
    rw [case_tree instr id position env (readSlots position env) (fun _ => rfl),
      case_tree instr (oldLabel 2) position env (readSlots position env) (fun _ => rfl)]
    apply bind_congr
    intro out
    have identity : Sum.map id (fun state : BlockInput α blocks => (id state.1, state.2)) out = out := by
      cases out <;> rfl
    rw [identity]
    exact (routes out).symm
  let req := m.selection.request
  have leaf (env : Env α) :
      (region instr env req.row.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr env req.jump >>= fun out => newFinish (splitTransfer (blocks + 2) out)) := by
    let vals : Values m.selection.scope α := readSlots position env
    let start : BlockInput α (blocks + 2) := (freshLabel blocks (0 : Fin 2), req.frame.pack vals)
    let body := step instr ambient m.code
    let phases := partitionStepByTarget body (inFresh blocks)
    have chain := follow instr ambient m.code (inFresh blocks) (oldLabel 2) (old_outside 2)
      req.row req.frame vals (freshLabel blocks)
      (fun i packet => by simp [inFresh, freshLabel]) m.leaf_eq
    have flatten : iter body start = iter phases start >>= newFinish := by
      change iter body start = iter phases start >>= Sum.elim pure (iter body)
      rw [← iter_partition_target body (inFresh blocks)]
      exact congrFun (iterate_fixpoint (iter phases)) _
    change (region instr env req.row.erase >>= fun out => oldFinish (splitTransfer blocks out)) = _
    have unsplit := unsplit_step instr req.row env vals (fun _ => rfl)
    have original :
        (region instr env req.row.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
          req.row.run instr vals >>= oldFinish := by
      rw [← unsplit]
      simp only [bind_assoc, pure_bind]
    have outlined :
        (region instr env req.jump >>= fun out => newFinish (splitTransfer (blocks + 2) out)) =
          iter body start := by
      simp only [Request.jump, region, pack_scope, pure_bind]
      change newFinish (splitTransfer (blocks + 2) ((freshLabel blocks (0 : Fin 2)).val, _)) = _
      rw [local_transfer]
      rfl
    change iter phases start = _ at chain
    rw [original, outlined, flatten, chain]
    simp only [map_eq_pure_bind, bind_assoc, pure_bind]
    exact bind_congr fun out => (routes out).symm
  have path_eq {Γ : List PacketType} (path : Path packets outputs m.selection.scope Γ) (env : Env α) :
      (region instr env (path.erase id req.row.erase) >>= fun out => oldFinish (splitTransfer blocks out)) =
      (region instr env (path.erase (oldLabel 2) req.jump) >>= fun out => newFinish (splitTransfer (blocks + 2) out)) := by
    induction path generalizing env with
    | here => exact leaf env
    | left test selected other ih =>
      exact case_congr instr env _ _ _ _ _ _ _ (fun value => ih (extend env value))
        (fun value => bypass other (extend env value))
    | right test other selected ih =>
      exact case_congr instr env _ _ _ _ _ _ _ (fun value => bypass other (extend env value))
        (fun value => ih (extend env value))
  change (region instr ambient source.entry.erase >>= fun out => oldFinish (splitTransfer blocks out)) =
    (region instr ambient m.code.entry.erase >>= fun out => newFinish (splitTransfer (blocks + 2) out))
  rw [m.sourceEntry, m.entry_eq]
  exact path_eq m.selection.path ambient

theorem preserves_run (m : Outlined sig context packets outputs source)
    (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env m.code.erase :=
  outlined_entry m instr env

theorem compiled_seed {A : Type 1} {Events : Type → Type}
    (built : Compiled sig context packets outputs source) (instr : Primitive Events F A) (env : Env A) :
    packetValue env built.publicReadback.provenance.seed = Silmaril.Isotope.Bridge.NamedFlat.Capture.packEnv captures env :=
  BranchEntry.seed_from_entry instr env _
    (Region.br.inj (built.publicReadback.provenance.sourceEntry.symm.trans built.prepared.emitted.entry_eq)).2

end EffectfulEntry

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
