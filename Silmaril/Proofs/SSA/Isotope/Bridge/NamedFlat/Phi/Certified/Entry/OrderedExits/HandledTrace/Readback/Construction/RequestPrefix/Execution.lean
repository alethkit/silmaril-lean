module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend extend_zero extend_succ)
open LambdaSSA.Semantics.Interaction (BlockInput Primitive Transfer region splitTransfer term)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible (Expr PacketType PrimitiveSignature Slot)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint)

universe u w
variable {E : Type w → Type w} {F : Type} {α : Type u}
  {Γ : List PacketType} {exits blocks captures : Nat}
  {sig : PrimitiveSignature F} {outputs : Fin exits → PacketType}

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

private theorem unsplit_step (instr : Primitive E F α) (row : Row sig outputs Γ)
    (env : Env α) (values : Values Γ α)
    (agree : ∀ {τ} (slot : Slot Γ τ), env (position slot) = values slot) :
    (region instr env (row.erase blocks) >>= fun out => pure (splitTransfer blocks out)) =
      (row.run instr values >>= fun out => pure (.inl out)) := by
  induction row generalizing env with
  | exit port value =>
    simp only [Row.erase, region, operand_tree instr position env values value agree, pure_bind,
      exit_transfer, Row.run]
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

private theorem follow (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (row : Row sig outputs Γ)
    (frame : Frame Γ) (values : Values Γ α) (labels : Fin (row.requests + 1) → Fin blocks)
    (rows : ∀ i, (graph.block (labels i)).erase = (row.cells blocks frame (fun j => (labels j).val) i).2) :
    iter (step instr env graph) (labels 0, frame.pack values) = row.run instr values := by
  induction row with
  | exit port value =>
    rw [congrFun (iterate_fixpoint (step instr env graph)) (labels 0, frame.pack values)]
    simp only [step, rows 0, Row.cells]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    simp only [region, operand_tree instr _ _ values value (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, exit_transfer, Sum.elim_inl, Row.run]
  | request op arg tail ih =>
    rw [congrFun (iterate_fixpoint (step instr env graph)) (labels 0, frame.pack values)]
    simp only [step, rows 0, Row.cells, Fin.cases_zero]
    rw [unpack_tree instr frame values _ 0 _ rfl]
    have saved : frame.load values (extend env (frame.pack values)) frame.shift = frame.pack values := by
      simpa only [Nat.add_zero, extend_zero] using
        load_ambient frame values (extend env (frame.pack values)) 0
    simp only [region, term, operand_tree instr _ _ values arg (load_slot frame values (extend env (frame.pack values)) 0 rfl),
      pure_bind, bind_assoc, extend_succ, extend_zero, saved, local_transfer, Sum.elim_inr, Row.run]
    apply bind_congr
    intro reply
    exact ih (.push (sig.reply op) frame) (bindReply values reply) (labels ∘ Fin.succ)
      (fun i => by
        have next := rows i.succ
        simp only [Row.cells] at next
        erw [Fin.cases_succ] at next
        exact next)

variable {packets : Fin blocks → PacketType} {source : FiniteCFG F blocks exits captures}
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

private theorem first_packet (row : Row sig outputs Γ) (frame : Frame Γ)
    (labels : Fin (row.requests + 1) → Nat) :
    (row.cells blocks frame labels 0).1 = frame.packet := by
  cases row <;> rfl

theorem old_packet (i : Fin blocks) : (s.table (oldLabel s.row.requests i)).1 = packets i := by
  by_cases selected : i = s.selected
  · subst i
    change (s.table (chainLabel s.selected s.row.requests 0)).1 = _
    rw [table_chain]
    exact first_packet _ _ _
  · rw [table_old s i selected]

private theorem entry_run (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (start : Fin blocks) (seed : LambdaSSA.Tm F)
    (entry : graph.entry.erase = .br start.val seed) :
    region instr env graph.erase =
      term instr env seed >>= fun packet => iter (step instr env graph) (start, packet) := by
  simp only [FiniteCFG.erase, region, entry, bind_assoc, pure_bind, local_transfer, Sum.elim_inr]
  rfl

private theorem selected_run (instr : Primitive E F α) (env : Env α) (packet : Value α) :
    iter (step instr env source) (s.selected, packet) =
      iter (step instr env emitted.code) (oldLabel s.row.requests s.selected, packet) := by
  let values : Values [packets s.selected] α := readSlots position (extend env packet)
  calc
    _ = s.row.run instr values := by
      rw [congrFun (iterate_fixpoint (step instr env source)) (s.selected, packet)]
      change ((region instr (extend env packet) (source.block s.selected).erase >>= fun out =>
        pure (splitTransfer blocks out)) >>= _) = _
      rw [s.row_eq, unsplit_step instr s.row (extend env packet) values (fun _ => rfl)]
      simp only [bind_assoc, pure_bind, Sum.elim_inl, bind_pure]
    _ = _ := (follow instr env emitted.code s.row (.entry (packets s.selected)) values
      (chainLabel s.selected s.row.requests) fun i => by
        rw [emitted.row_eq, table_chain]
        rfl).symm

private theorem jump_run (instr : Primitive E F α) (env : Env α)
    (graph : FiniteCFG F blocks exits captures) (here there : Fin blocks) (packet : Value α)
    (arg : LambdaSSA.Tm F) (row : (graph.block here).erase = .br there.val arg) :
    iter (step instr env graph) (here, packet) =
      term instr (extend env packet) arg >>= fun out => iter (step instr env graph) (there, out) := by
  rw [congrFun (iterate_fixpoint (step instr env graph)) (here, packet)]
  simp only [step, row, region, bind_assoc, pure_bind, local_transfer, Sum.elim_inr]

private theorem route_run (instr : Primitive E F α) (env : Env α) {here : Fin blocks}
    (route : Route source s.selected here) (packet : Value α) :
    iter (step instr env source) (here, packet) =
      iter (step instr env emitted.code) (oldLabel s.row.requests here, packet) := by
  induction route generalizing packet with
  | done => exact selected_run s emitted instr env packet
  | jump here next arg other row tail ih =>
    have moved : (emitted.code.block (oldLabel s.row.requests here)).erase =
        .br (oldLabel s.row.requests next).val arg := by
      rw [emitted.row_eq, table_old s here other, row]
      simp [Region.renameLabels, moveExit, next.isLt, oldLabel]
    rw [jump_run instr env source here next packet arg row,
      jump_run instr env emitted.code _ _ packet arg moved]
    exact bind_congr ih

theorem preserves_run (instr : Primitive E F α) (env : Env α) :
    region instr env source.erase = region instr env emitted.code.erase := by
  rw [entry_run instr env source s.entry _ s.entry_eq,
    entry_run instr env emitted.code (oldLabel s.row.requests s.entry) _ (emitted.entry_eq.trans s.entry_eq)]
  exact bind_congr (route_run s emitted instr env s.route)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix
