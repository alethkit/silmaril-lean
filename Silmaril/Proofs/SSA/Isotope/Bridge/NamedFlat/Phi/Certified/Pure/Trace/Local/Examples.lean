module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Thms

/-! The right graph renames every register and block and inserts a silent entry block. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Pending Row br ret)
open Silmaril.Elgot.ITree (Tree Trace TraceLE HasTrace vis vis_bind resume resume_body
  hasTrace_vis_exchange_iff hasTrace_vis_request)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)

private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Nat
private abbrev Atom := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private abbrev Store := Reg → Value Atom
private abbrev State := Pending Reg Key (Value Atom)

private inductive Opcode
  | tick

private inductive Event : Type → Type
  | tick (argument : Nat) : Event (Nat ⊕ Nat)

private def atom (n : Nat) : Value Atom := .atom ⟨n⟩
private def num : Ty SortName := .base ⟨()⟩
private def inputTypes : BoundCtx (Ty SortName) 1 := .snoc .nil num
private def headerType : Ty SortName := .product (.product num .unit) (.product num .unit)
private def shimType : Ty SortName := .product .unit (.product num .unit)

private instance : HasTy Opcode (Ty SortName) where
  src _ := num
  trg _ := .coprod num num

private def instr : Primitive Event Opcode Atom
  | .tick, .atom argument => vis (.tick argument.down) fun
      | .inl a => pure (.inl (atom a))
      | .inr a => pure (.inr (atom a))
  | _, _ => Silmaril.Elgot.ITree.diverge

private def seedName (right : Bool) : Reg := if right then ⟨10⟩ else ⟨0⟩
private def phiName (right : Bool) : Reg := if right then ⟨11⟩ else ⟨1⟩
private def doneName (right : Bool) : Reg := if right then ⟨12⟩ else ⟨2⟩
private def backName (right : Bool) : Reg := if right then ⟨13⟩ else ⟨3⟩
private def header (right : Bool) : Key := if right then ⟨11⟩ else ⟨1⟩
private def shim : Key := ⟨10⟩

private def predecessor (right back : Bool) : Option Key :=
  if back then some (header right) else if right then some shim else none

private def headerRow (right : Bool) : Row Reg Key :=
  ⟨phiName right, [(predecessor right false, .var (seedName right)),
    (predecessor right true, .var (backName right))]⟩

private theorem header_operand (right back : Bool) :
    (headerRow right).operand (predecessor right back) =
      .var (if back then backName right else seedName right) := by
  cases right <;> cases back <;> rfl

private def headerBlock (right : Bool) : Block Reg Key Opcode :=
  ⟨[headerRow right], .term (.case (.app .tick (.var (phiName right))) (doneName right)
      (ret (.var (doneName right))) (backName right) (br (header right)))⟩

private def shimBlock : Block Reg Key Opcode := ⟨[], .term (br (header true))⟩

private def graph (right : Bool) : Graph Reg Key Opcode :=
  if right then ⟨.term (br shim), [(shim, shimBlock), (header true, headerBlock true)]⟩
  else ⟨.term (br (header false)), [(header false, headerBlock false)]⟩

private def names (right : Bool) : Fin 1 → Option Reg := fun _ => some (seedName right)

private def admitLeft := Certified.admit (graph false) [seedName false] [(header false, [])]
  (names false) inputTypes (fun _ => headerType) (fun _ => num)

private def admitRight := Certified.admit (graph true) [seedName true]
  [(shim, [seedName true]), (header true, [])] (names true) inputTypes
  (fun i => if i.val = 0 then shimType else headerType) (fun _ => num)

private def closedLeft := (close (admitLeft.get (by decide))).get (by decide)
private def closedRight := (close (admitRight.get (by decide))).get (by decide)

private def sourceStore (seed : Nat) : Store := fun _ => atom seed
private def inputs (seed : Nat) : MatchedInputs (α := Atom) inputTypes inputTypes
    (fun _ => num) (fun _ => num) (names false) (names true) :=
  ⟨⟨rfl, rfl⟩, sourceStore seed, sourceStore seed, fun _ => rfl⟩

private def pending (right back : Bool) (store : Store) : State :=
  (.jump (predecessor right back) (header right), store)

private def operand (right back : Bool) (store : Store) : Value Atom :=
  store (if back then backName right else seedName right)

private def afterTick (right : Bool) (store : Store) (argument : Nat) : Nat ⊕ Nat → State :=
  let updated := upd store (phiName right) (atom argument)
  fun
  | .inl answer => (.returned (atom answer), upd updated (doneName right) (atom answer))
  | .inr answer => pending right true (upd updated (backName right) (atom answer))

private theorem header_step (right back : Bool) (store : Store) (argument : Nat)
    (reads : operand right back store = atom argument) :
    stepTree instr (graph right) (pending right back store) =
      vis (.tick argument) (fun reply => pure (.inr (afterTick right store argument reply))) := by
  have found : (graph right).blocks.lookup (header right) = some (headerBlock right) := by
    cases right <;> rfl
  rw [pending, step_jump _ _ _ _ _ found]
  simp only [headerBlock, CFG.Cyclic.Phi.assign, header_operand]
  cases right <;> cases back <;>
    simp [operand, seedName, backName] at reads <;>
    simp [CFG.Cyclic.Phi.execute, headerRow, predecessor, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      treeModel, instr, atom, br, ret, afterTick, pending, upd, reads, seedName, backName,
      doneName, phiName, ← bind_pure_comp, bind_assoc, vis_bind]
  all_goals
    funext reply
    cases reply <;> simp only [pure_bind]

private theorem after_back_operand (right : Bool) (store : Store) (argument reply : Nat) :
    operand right true (afterTick right store argument (.inr reply)).2 = atom reply := by
  simp [afterTick, operand, pending, upd]

private theorem entry_left (store : Store) :
    entryTree instr (graph false) store = pure (.inr (pending false false store)) := by
  simp [entryTree, graph, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br, pending, predecessor]

private theorem entry_right (store : Store) :
    entryTree instr (graph true) store = pure (.inr (.jump none shim, store)) := by
  simp [entryTree, graph, CFG.Cyclic.Phi.execute, CFG.Body.exec, CFG.Term.exec, br]

private theorem shim_step (store : Store) :
    stepTree instr (graph true) (.jump none shim, store) = pure (.inr (pending true false store)) := by
  rw [step_jump _ _ _ _ _ (block := shimBlock) rfl]
  simp [shimBlock, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign, CFG.Body.exec, CFG.Term.exec,
    br, pending, predecessor]

-- At a header, the selected operands have the common numeric base shape and
-- value. The relation aligns the entry and backedge keys through predecessor.
private inductive Boundary : State → State → Prop where
  | header {back : Bool} {left right : Store} {argument : Nat}
      (readsLeft : operand false back left = atom argument)
      (readsRight : operand true back right = atom argument) :
      Boundary (pending false back left) (pending true back right)
  | returns (answer : Nat) (left right : Store) :
      Boundary (.returned (atom answer), left) (.returned (atom answer), right)

private inductive Residual : Tree Event (BodyResult Reg Key Atom) → Tree Event (BodyResult Reg Key Atom) → Prop where
  | entry (seed : Nat) :
      Residual (entryTree instr (graph false) (sourceStore seed))
        (entryTree instr (graph true) (sourceStore seed))
  | tick (left right : Store) (argument : Nat) :
      Residual (vis (.tick argument) (fun r => pure (.inr (afterTick false left argument r))))
        (vis (.tick argument) (fun r => pure (.inr (afterTick true right argument r))))
  | reply (left right : Store) (argument : Nat) (reply : Nat ⊕ Nat) :
      Residual (pure (.inr (afterTick false left argument reply)))
        (pure (.inr (afterTick true right argument reply)))
  | exit (answer : Nat) : Residual (pure (.inl (0, .inl (atom answer))))
      (pure (.inl (0, .inl (atom answer))))

private def simulation : Simulation instr instr (graph false) (graph true) where
  boundary := Boundary
  residual := Residual
  atBoundary := by
    intro l r paired
    cases paired with
    | header readsLeft readsRight =>
      rw [header_step _ _ _ _ readsLeft, header_step _ _ _ _ readsRight]
      exact .tick _ _ _
    | returns answer left right =>
      rw [step_return, step_return]
      exact .exit answer
  inspect := by
    intro l r related
    cases related with
    | entry seed =>
      rw [entry_left, entry_right]
      apply Layer.edge (rightPending := pending true false (sourceStore seed))
      · apply Silent.more
        rw [shim_step]
        exact .refl _
      · exact .header (argument := seed) rfl rfl
    | tick left right argument => exact .request _ (.refl _) (.reply left right argument)
    | reply left right argument reply =>
      cases reply with
      | inl answer => exact .edge (.refl _) (.returns answer _ _)
      | inr answer =>
        apply Layer.edge (.refl _)
        exact .header (after_back_operand false left argument answer)
          (after_back_operand true right argument answer)
    | exit => exact .exit (.refl _)

private theorem packed_le (seed : Nat) :
    TraceLE (packedObservation closedLeft instr (inputs seed).leftStore)
      (packedObservation closedRight instr (inputs seed).rightStore) :=
  simulation.packed_le closedLeft closedRight (inputs seed) (Residual.entry seed)

private def twoTicks : Trace Event (Transfer Atom) :=
  .exchange (.tick 4) (.inr 2) (.request (.tick 2))

private theorem source_two_ticks :
    HasTrace (sourceObservation instr (graph false) (sourceStore 4)) twoTicks := by
  rw [sourceObservation_eq_resume, entry_left, twoTicks]
  let initial := pending false false (sourceStore 4)
  have enter :
      resume (stepTree instr (graph false)) (pure (.inr initial)) =
        resume (stepTree instr (graph false)) (stepTree instr (graph false) initial) := by
    rw [resume_body]
    simp [resume]
  rw [enter, show initial = pending false false (sourceStore 4) from rfl,
    header_step false false (sourceStore 4) 4 rfl]
  simp only [resume, vis_bind, hasTrace_vis_exchange_iff, pure_bind, Sum.elim_inr]
  rw [← resume_body]
  change HasTrace (resume (stepTree instr (graph false))
    (stepTree instr (graph false) (pending false true (afterTick false (sourceStore 4) 4 (.inr 2)).2))) _
  rw [header_step false true _ 2 (after_back_operand false (sourceStore 4) 4 2)]
  simp only [resume, vis_bind]
  exact hasTrace_vis_request _ _

-- The extra right entry block is silent. The second request still uses the
-- reply bound on the right self-edge, through the renamed φ destination.
private theorem packed_two_ticks :
    HasTrace (packedObservation closedRight instr (inputs 4).rightStore) twoTicks :=
  packed_le 4 twoTicks (by
    rw [packedObservation_eq_sourceObservation]
    exact source_two_ticks)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Examples
