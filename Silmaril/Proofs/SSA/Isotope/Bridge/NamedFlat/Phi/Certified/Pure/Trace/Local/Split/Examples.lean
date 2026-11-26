module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Admission.Thms

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

private def tickBody (next : Key) : CFG.Body Reg (Option Key) Opcode :=
  .term (.case (.app .tick (.pair (.var x) (.var y)))
    doneName (ret (.var doneName)) backName (br next))

private def headerBlock : Block Reg Key Opcode :=
  ⟨[⟨x, [(none, .var seedX), (some header, .var y)]⟩,
    ⟨y, [(none, .var seedY), (some header, .var x)]⟩], tickBody header⟩

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

private def response (next : Key) (store : Store) : Nat ⊕ Unit → State
  | .inl result => (.returned (atom result), upd store doneName (atom result))
  | .inr _ => (.jump (some header) next, upd store backName .unit)

private theorem tick_step_of (graph : Graph Reg Key Opcode) (next : Key)
    (pred : Option Key) (store : Store) (a b : Nat) {block : Block Reg Key Opcode}
    (found : graph.blocks.lookup header = some block) (body : block.body = tickBody next)
    (assigned : assign (treeModel instr) pred store block.rows store = writePair store a b) :
    stepTree instr graph (.jump pred header, store) =
      vis (.tick a b) (fun reply => pure (.inr (response next (writePair store a b) reply))) := by
  rw [step_jump _ _ _ _ _ found, assigned, body]
  simp [CFG.Cyclic.Phi.execute, tickBody, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
    treeModel, instr, writePair, upd, x, y, atom, ← bind_pure_comp, bind_assoc, vis_bind]
  funext reply
  cases reply <;> simp [response, br, ret, CFG.Term.exec, Val.eval, upd, atom]

private theorem tick_step (pred : Option Key) (store : Store) (a b : Nat)
    (assigned : assign (treeModel instr) pred store headerBlock.rows store = writePair store a b) :
    stepTree instr source (.jump pred header, store) =
      vis (.tick a b) (fun reply => pure (.inr (response header (writePair store a b) reply))) :=
  tick_step_of source header pred store a b rfl rfl assigned

private theorem resume_transfer {source : Graph Reg Key Opcode} (p : State) :
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

private def init : Key := ⟨16⟩
private def latch : Key := ⟨18⟩

private def jumpBlock (target : Key) : Block Reg Key Opcode := ⟨[], .term (br target)⟩

private def distinctHeader : Block Reg Key Opcode :=
  ⟨[⟨x, [(some latch, .var y), (some init, .var seedX)]⟩,
    ⟨y, [(some latch, .var x), (some init, .var seedY)]⟩], tickBody latch⟩

-- The latch precedes the unaffected predecessor in table order, so the
-- split must keep its original position in each incoming row.
private def distinctSource : Graph Reg Key Opcode :=
  ⟨.term (br init), [(latch, jumpBlock header), (header, distinctHeader), (init, jumpBlock header)]⟩

private def distinctPlan : Plan Reg Reg Key (Option Key) := { plan with predecessor := some latch }
private def distinctTarget : Graph Reg (Option Key) Opcode := distinctPlan.rewrite distinctSource
private theorem distinctChecked : Checked distinctPlan distinctSource distinctTarget :=
  distinctPlan.check_sound (by decide)

example : distinctTarget.predecessors (plan.label header) =
    [some plan.forward, some (plan.label init)] := by decide

example :
    (distinctTarget.blocks.lookup (plan.label header)).map (fun block =>
      CFG.Cyclic.Phi.arguments (some (plan.label init)) block.rows) =
      some [.var (plan.register seedX), .var (plan.register seedY)] := by decide

private def parallel : Graph Reg Key Opcode :=
  { distinctSource with blocks :=
      [(latch, ⟨[], .term (.case (.app .tick (.pair (.var x) (.var y)))
        ⟨20⟩ (br header) ⟨21⟩ (br header))⟩), (header, distinctHeader), (init, jumpBlock header)] }

example : distinctPlan.hasEdge parallel = true ∧
    distinctPlan.check parallel (distinctPlan.rewrite parallel) = false := by decide

-- The unnamed entry can also be split, including its incoming φ column.
private def entryPlan : Plan Reg Reg Key (Option Key) := { plan with predecessor := none }

example : sourceObservation instr source originalStore =
    sourceObservation instr (entryPlan.rewrite source) (entryPlan.renameStore originalStore) :=
  source_eq (entryPlan.check_sound (by decide)) instr originalStore

private def blockProfile (headerIndex : Nat) (index : Nat) : Ty SortName :=
  .product (if index = headerIndex then pairPacket else .unit) (.product num (.product num pairPacket))

private def distinctAdmittedLeft := (Certified.admit distinctSource [seedX, seedY]
  [(latch, [x, y]), (header, []), (init, [seedX, seedY])] captures profile
  (fun i => blockProfile 1 i.val) exits).get (by decide)

private def distinctAdmittedRight := (Certified.admit distinctTarget ([seedX, seedY].map plan.register)
  [(plan.forward, [plan.register x, plan.register y]), (plan.label latch, [plan.register x, plan.register y]),
    (plan.label header, []), (plan.label init, [plan.register seedX, plan.register seedY])]
  renamedCaptures profile (fun i => blockProfile 2 i.val) exits).get (by decide)

private def distinctClosedLeft := (close distinctAdmittedLeft).get (by decide)
private def distinctClosedRight := (close distinctAdmittedRight).get (by decide)

private theorem distinctAlignment :
    InputAlignment distinctPlan profile profile exits exits captures renamedCaptures :=
  ⟨⟨rfl, rfl⟩, fun _ => rfl⟩

private theorem distinct_packed_same (store : Store) :
    packedObservation distinctClosedLeft instr store =
      packedObservation distinctClosedRight instr (distinctPlan.renameStore store) :=
  packed_eq distinctChecked instr distinctClosedLeft distinctClosedRight distinctAlignment store

private theorem straight_step (pred : Option Key) (target next : Key) (store : Store)
    (found : distinctSource.blocks.lookup target = some (jumpBlock next)) :
    stepTree instr distinctSource (.jump pred target, store) =
      pure (.inr (.jump (some target) next, store)) := by
  rw [step_jump _ _ _ _ _ found]
  simp [jumpBlock, assign, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]

private theorem distinct_source_swap :
    HasTrace (sourceObservation instr distinctSource originalStore) swappedTrace := by
  have entry : entryTree instr distinctSource originalStore =
      pure (.inr (.jump none init, originalStore)) := by
    simp [entryTree, distinctSource, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]
  rw [sourceObservation_eq_resume, entry, resume_transfer, straight_step none init header _ rfl,
    resume_transfer, tick_step_of distinctSource latch (some init) originalStore 2 5
      (block := distinctHeader) rfl rfl rfl, swappedTrace]
  simp only [resume, vis_bind, hasTrace_vis_exchange_iff, pure_bind, Sum.elim_inr]
  rw [← resume_body]
  change HasTrace (resume (stepTree instr distinctSource)
    (stepTree instr distinctSource (.jump (some header) latch,
      upd (writePair originalStore 2 5) backName .unit))) _
  rw [straight_step (some header) latch header _ rfl, resume_transfer,
    tick_step_of distinctSource latch (some latch) _ 5 2 (block := distinctHeader) rfl rfl rfl]
  simp only [resume, vis_bind]
  exact hasTrace_vis_request _ _

private theorem distinct_packed_swap :
    HasTrace (packedObservation distinctClosedRight instr (distinctPlan.renameStore originalStore)) swappedTrace := by
  rw [← distinct_packed_same, packedObservation_eq_sourceObservation]
  exact distinct_source_swap

private def seedCaptures (i : Fin 2) : Option Reg := some ⟨i.val⟩
private def seedTypes : BoundCtx (Ty SortName) 2 := .snoc (.snoc .nil num) num
private def arrivals : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(header, [])]

private def seedAdmission := (Certified.admit source [seedX, seedY] arrivals
  seedCaptures seedTypes originalProfile exits).get (by decide)

private def seedClosed := (close seedAdmission).get (by decide)

-- Plain renaming cannot supply the version-zero copies of x and y now read
-- by the generated lexical entry's packet construction.
example : (NamedFlat.compile (CFG.Cyclic.Phi.lower target) [none]
    (fun i : Fin 2 => (seedCaptures i).map plan.register)).isNone := by decide

-- The forwarding block also needs a certified arrival claim for those reads.
example : CFG.Cyclic.Phi.GlobalSSA.check target ([seedX, seedY].map plan.register)
    [(plan.label header, [])] = false := by decide

private def generated := (generate plan seedAdmission arrivals).get (by decide)

example : generated.extra =
    [(some (plan.register y), num), (some (plan.register x), num)] := by decide

private theorem generated_packed_swap :
    HasTrace (packedObservation generated.closed instr (plan.renameStore originalStore)) swappedTrace := by
  rw [← generated.packed_eq seedClosed instr originalStore, packedObservation_eq_sourceObservation]
  exact source_swap

-- The distinct latch already causes both variables to occur in the old
-- versioner's support. Splitting it reuses all old capture positions.
private def distinctGenerated := (generate distinctPlan distinctAdmittedLeft
  [(latch, [x, y]), (header, []), (init, [seedX, seedY])]).get (by decide)

example : distinctGenerated.extra = [] := by decide

example : (generate entryPlan seedAdmission arrivals).isSome := by decide

-- An old, unused capture may carry a type that cannot type a newly live
-- version-zero read. Generation keeps that interface and rejects it.
private def incompatibleTypes : BoundCtx (Ty SortName) 4 :=
  .ofFin (fun i => if i.val = 2 then .unit else num)

private def incompatibleAdmission := (Certified.admit source [seedX, seedY] arrivals
  captures incompatibleTypes originalProfile exits).get (by decide)

example : (generate plan incompatibleAdmission arrivals).isNone := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.Examples
