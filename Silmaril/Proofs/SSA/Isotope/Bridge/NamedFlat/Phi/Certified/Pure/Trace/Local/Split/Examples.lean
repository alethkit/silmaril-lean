module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Thms

/-! A visible loop swaps two live values on the split self-edge. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Pending assign br ret)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree Trace HasTrace vis vis_bind resume resume_body
  hasTrace_vis_exchange_iff hasTrace_vis_request)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)

private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private abbrev Store := Reg → Value Atom

private inductive Opcode
  | tick
  deriving DecidableEq

private inductive Event : Type → Type
  | tick (left right : Nat) : Event (Nat ⊕ Unit)

private def atom (n : Nat) : Value Atom := .atom ⟨n⟩
private def num : Ty SortName := .base ⟨()⟩

private instance : HasTy Opcode (Ty SortName) where
  src _ := .product num num
  trg _ := .coprod num .unit

private def instr : Primitive Event Opcode Atom
  | .tick, .pair (.atom left) (.atom right) => vis (.tick left.down right.down) fun
      | .inl result => pure (.inl (atom result))
      | .inr _ => pure (.inr .unit)
  | _, _ => Silmaril.Elgot.ITree.diverge

private def seedX : Reg := ⟨0⟩
private def seedY : Reg := ⟨1⟩
private def x : Reg := ⟨2⟩
private def y : Reg := ⟨3⟩
private def doneName : Reg := ⟨4⟩
private def backName : Reg := ⟨5⟩
private def header : Key := ⟨17⟩

private def headerBlock : Block Reg Key Opcode :=
  ⟨[⟨x, [(none, .var seedX), (some header, .var y)]⟩,
    ⟨y, [(none, .var seedY), (some header, .var x)]⟩],
    .term (.case (.app .tick (.pair (.var x) (.var y)))
      doneName (ret (.var doneName)) backName (br header))⟩

private def source : Graph Reg Key Opcode := ⟨.term (br header), [(header, headerBlock)]⟩

private def plan : Plan Reg Reg Key (Option Key) where
  register := ((Equiv.swap seedX ⟨8⟩).trans (Equiv.swap seedY ⟨9⟩)).trans
    ((Equiv.swap x ⟨6⟩).trans (Equiv.swap y ⟨7⟩))
  label := ⟨some, fun _ _ h => Option.some.inj h⟩
  header := header
  forward := none
  fresh := fun _ => Option.some_ne_none _

private def target : Graph Reg (Option Key) Opcode := plan.rewrite source

private theorem checked : Checked plan source target := plan.check_sound (by decide)

-- Reusing the pre-split key at the header is rejected.
private def stale : Graph Reg (Option Key) Opcode :=
  ⟨target.entry, target.blocks.map fun (key, block) =>
    (key, ⟨block.rows.map fun row => ⟨row.dst,
      row.incoming.map fun (pred, value) =>
        (if pred = some plan.forward then some (plan.label header) else pred, value)⟩, block.body⟩)⟩

example : plan.check source stale = false := by decide

private def captures (i : Fin 4) : Option Reg := some ⟨i.val⟩
private def renamedCaptures (i : Fin 4) : Option Reg := (captures i).map plan.register
private def profile : BoundCtx (Ty SortName) 4 := .snoc (.snoc (.snoc (.snoc .nil num) num) num) num
private def exits : Fin 1 → Ty SortName := fun _ => num
private def pairPacket : Ty SortName := .product num (.product num .unit)
private def originalProfile (_ : Fin (blockCount source)) : Ty SortName :=
  .product pairPacket pairPacket

-- The cyclic versioner carries the global tuple of free registers. After
-- splitting, the forwarding block's use of x and y adds them to the tuple.
private def splitProfile (i : Fin (blockCount target)) : Ty SortName :=
  .product (if i.val = 0 then .unit else pairPacket) (.product num (.product num pairPacket))

private def admittedLeft := (Certified.admit source [seedX, seedY] [(header, [])]
  captures profile originalProfile exits).get (by decide)

private def admittedRight := (Certified.admit target ([seedX, seedY].map plan.register)
  [(plan.forward, [plan.register x, plan.register y]), (plan.label header, [])]
  renamedCaptures profile splitProfile exits).get (by decide)

private def closedLeft := (close admittedLeft).get (by decide)
private def closedRight := (close admittedRight).get (by decide)

private theorem alignment : InputAlignment plan profile profile exits exits captures renamedCaptures :=
  ⟨⟨rfl, rfl⟩, fun _ => rfl⟩

private theorem packed_same (store : Store) :
    packedObservation closedLeft instr store =
      packedObservation closedRight instr (plan.renameStore store) :=
  packed_eq checked instr closedLeft closedRight alignment store

private abbrev State := Pending Reg Key (Value Atom)

private def originalStore : Store := fun name =>
  if name = seedX then atom 2 else if name = seedY then atom 5 else atom 0

private def writePair (store : Store) (a b : Nat) : Store := upd (upd store x (atom a)) y (atom b)

private def response (store : Store) : Nat ⊕ Unit → State
  | .inl result => (.returned (atom result), upd store doneName (atom result))
  | .inr _ => (.jump (some header) header, upd store backName .unit)

private theorem tick_step (pred : Option Key) (store : Store) (a b : Nat)
    (assigned : assign (treeModel instr) pred store headerBlock.rows store = writePair store a b) :
    stepTree instr source (.jump pred header, store) =
      vis (.tick a b) (fun reply => pure (.inr (response (writePair store a b) reply))) := by
  rw [step_jump _ _ _ _ _ (block := headerBlock) rfl, assigned]
  simp [CFG.Cyclic.Phi.execute, headerBlock, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    treeModel, instr, writePair, upd, x, y, atom, ← bind_pure_comp, bind_assoc, vis_bind]
  funext reply
  cases reply <;> simp [response, br, ret, CFG.Term.exec, Val.eval, upd, atom]

private theorem resume_transfer (p : State) :
    resume (stepTree instr source) (pure (.inr p)) =
      resume (stepTree instr source) (stepTree instr source p) := by
  rw [resume_body]
  simp [resume]

private def swappedTrace : Trace Event (Transfer Atom) :=
  .exchange (.tick 2 5) (.inr ()) (.request (.tick 5 2))

private theorem source_swap :
    HasTrace (sourceObservation instr source originalStore) swappedTrace := by
  have entry : entryTree instr source originalStore =
      pure (.inr (.jump none header, originalStore)) := by
    simp [entryTree, source, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]
  rw [sourceObservation_eq_resume, entry, resume_transfer, tick_step none originalStore 2 5 rfl,
    swappedTrace]
  simp only [resume, vis_bind, hasTrace_vis_exchange_iff, pure_bind, Sum.elim_inr]
  rw [← resume_body]
  change HasTrace (resume (stepTree instr source)
    (stepTree instr source (.jump (some header) header,
      upd (writePair originalStore 2 5) backName .unit))) _
  rw [tick_step (some header) _ 5 2 rfl]
  simp only [resume, vis_bind]
  exact hasTrace_vis_request _ _

-- The second request follows the inserted forwarding block and exposes the
-- two different values in swapped order. Sequential writes would lose one.
private theorem packed_swap :
    HasTrace (packedObservation closedRight instr (plan.renameStore originalStore)) swappedTrace := by
  rw [← packed_same, packedObservation_eq_sourceObservation]
  exact source_swap

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.Examples
