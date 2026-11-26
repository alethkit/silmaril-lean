module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Thms

/-! Two certified dispatchers take the same visible backedges until one loses a request. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.TraceExamples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending br ret)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace TraceLE HasTrace vis vis_bind diverge iterate_fixpoint
  traceLE_diverge hasTrace_diverge_iff hasTrace_vis_exchange_iff hasTrace_vis_request)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.FiniteCFG (packedTreeOutput)

private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Unit
private abbrev Atom := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit
private abbrev Store := Reg → Value Atom
private abbrev State := Pending Reg Key (Value Atom)

private def atom (n : Nat) : Value Atom := .atom ⟨n⟩

private inductive Opcode
  | tick (total : Bool)

private inductive Event : Type → Type
  | tick (argument : Nat) : Event (Nat ⊕ Nat)

private def num : Ty SortName := .base ⟨()⟩
private def inputTypes : BoundCtx (Ty SortName) 1 := .snoc .nil num
private def headerType : Ty SortName := .product (.product num .unit) (.product num .unit)

private instance : HasTy Opcode (Ty SortName) where
  src _ := num
  trg _ := .coprod num num

private def replyValue : Nat ⊕ Nat → Value Atom
  | .inl answer => .inl (atom answer)
  | .inr answer => .inr (atom answer)

private def instr : Primitive Event Opcode Atom
  | .tick total, .atom argument =>
      if total || argument.down != 0 then vis (.tick argument.down) (pure ∘ replyValue)
      else diverge
  | _, _ => diverge

private def seedName : Reg := ⟨0⟩
private def phiName : Reg := ⟨1⟩
private def doneName : Reg := ⟨2⟩
private def backName : Reg := ⟨3⟩
private def header : Key := ⟨()⟩

private def graph (total : Bool) : Graph Reg Key Opcode :=
  ⟨.term (br header),
    [(header, ⟨[⟨phiName, [(none, .var seedName), (some header, .var backName)]⟩],
      .term (.case (.app (.tick total) (.var phiName))
        doneName (ret (.var doneName)) backName (br header))⟩)]⟩

private def certificate : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(header, [])]
private def names : Fin 1 → Option Reg := fun _ => some seedName

private def admit (total : Bool) :=
  Certified.admit (graph total) [seedName] certificate names inputTypes
    (fun _ => headerType) (fun _ => num)

private def partialAdmission := (admit false).get (by decide)
private def totalAdmission := (admit true).get (by decide)
private def partialClosed := (close partialAdmission).get (by decide)
private def totalClosed := (close totalAdmission).get (by decide)

private def sourceStore (seed : Nat) : Store := fun _ => atom seed

private def inputs (seed : Nat) :
    MatchedInputs (α := Atom) inputTypes inputTypes (fun _ => num) (fun _ => num) names names :=
  ⟨⟨rfl, rfl⟩, sourceStore seed, sourceStore seed, fun _ => rfl⟩

private def pending (back : Bool) (store : Store) : State :=
  (.jump (if back then some header else none) header, store)

private def operand (back : Bool) (store : Store) : Value Atom :=
  store (if back then backName else seedName)

private def afterTick (store : Store) (argument value : Value Atom) :
    Tree Event ((Option Key × Value Atom) ⊕ State) :=
  let updated := upd store phiName argument
  match value with
  | .inl reply => pure (.inr (.returned reply, upd updated doneName reply))
  | .inr reply => pure (.inr (pending true (upd updated backName reply)))
  | _ => diverge

private def sourceStep (total : Bool) := CFG.Cyclic.Phi.step (treeModel instr) (graph total)

private theorem tick_step (total back : Bool) (store : Store) :
    sourceStep total (pending back store) =
      (instr (.tick total) (operand back store) >>= afterTick store (operand back store)) := by
  cases back <;>
    simp [sourceStep, pending, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
      CFG.Cyclic.Phi.Row.operand, graph, List.lookup, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      treeModel, br, ret, operand, upd, seedName, backName, doneName, phiName,
      ← bind_pure_comp, bind_assoc]
  all_goals
    congr 1
    funext value
    cases value <;> simp [afterTick, pending, doneName, backName, phiName]

private theorem tick_le (value : Value Atom) :
    TraceLE (instr (.tick false) value) (instr (.tick true) value) := by
  cases value <;> try exact TraceLE.refl _
  simp only [instr]
  split
  · exact TraceLE.refl _
  · exact traceLE_diverge _

private theorem step_le (transfer : State) :
    TraceLE (sourceStep false transfer) (sourceStep true transfer) := by
  have atPending (back : Bool) (store : Store) :
      TraceLE (sourceStep false (pending back store)) (sourceStep true (pending back store)) := by
    rw [tick_step, tick_step]
    exact (tick_le _).bind_left _
  obtain ⟨control, store⟩ := transfer
  cases control with
  | returned value => exact TraceLE.refl _
  | jump pred target =>
      have ht : target = header := Subsingleton.elim _ _
      subst target
      cases pred with
      | none => exact atPending false store
      | some pred =>
          have hp : pred = header := Subsingleton.elim _ _
          subst pred
          exact atPending true store

private noncomputable def resume (total : Bool) (state : State) : Tree Event (Transfer Atom) :=
  iter (sourceStep total) state >>= fun p => pure (packedTreeOutput (treeExitNumber [none] p))

private theorem from_entry (total : Bool) (seed : Nat) :
    sourceObservation instr (graph total) (sourceStore seed) =
      resume total (pending false (sourceStore seed)) := by
  have entered : CFG.Cyclic.Phi.execute (treeModel instr) none
      (graph total).entry (sourceStore seed) = pure (pending false (sourceStore seed)) := rfl
  rw [sourceObservation, runTree, CFG.Cyclic.Phi.run, entered, pure_bind]
  rfl

private theorem source_le (seed : Nat) :
    TraceLE (sourceObservation instr (graph false) (sourceStore seed))
      (sourceObservation instr (graph true) (sourceStore seed)) := by
  rw [from_entry, from_entry]
  exact (TraceLE.iter step_le _).bind_pure _

example : ∀ seed : Nat, TraceLE (packedObservation partialClosed instr (inputs seed).leftStore)
    (packedObservation totalClosed instr (inputs seed).rightStore) :=
  (packed_pointwise_traceLE_iff partialClosed totalClosed instr instr inputs).2 source_le

private def nextStore (store : Store) (argument reply : Nat) : Store :=
  upd (upd store phiName (atom argument)) backName (atom reply)

private theorem nextOperand (store : Store) (argument reply : Nat) :
    operand true (nextStore store argument reply) = atom reply := by
  simp [operand, nextStore, upd]

private noncomputable def continueTick (total : Bool) (store : Store) (argument : Nat)
    (reply : Nat ⊕ Nat) : Tree Event (Transfer Atom) :=
  afterTick store (atom argument) (replyValue reply) >>=
    fun p => p.elim (fun out => pure (packedTreeOutput (treeExitNumber [none] out))) (resume total)

private theorem resume_at (total back : Bool) (store : Store) (argument : Nat)
    (reads : operand back store = atom argument) :
    resume total (pending back store) =
      if total || argument != 0 then vis (.tick argument) (continueTick total store argument)
      else diverge := by
  unfold resume
  rw [congrFun (iterate_fixpoint (sourceStep total)) (pending back store), tick_step, reads]
  simp only [instr, atom]
  split
  · simp only [bind_assoc, vis_bind, Function.comp_apply, pure_bind]
    congr 1
    funext reply
    cases reply <;> simp only [afterTick, replyValue, pure_bind, Sum.elim_inr, continueTick, resume, atom]
  · simp [-bind_pure_comp]

private theorem hasTrace_back_iff (total back : Bool) (store : Store) (argument reply : Nat)
    (reads : operand back store = atom argument) (enabled : (total || argument != 0) = true)
    (tail : Trace Event (Transfer Atom)) :
    HasTrace (resume total (pending back store)) (.exchange (.tick argument) (.inr reply) tail) ↔
      HasTrace (resume total (pending true (nextStore store argument reply))) tail := by
  rw [resume_at total back store argument reads, ite_eq_left enabled, hasTrace_vis_exchange_iff]
  simp only [continueTick, afterTick, replyValue, pure_bind, Sum.elim_inr, nextStore]

private def twoBackedges : Trace Event (Transfer Atom) :=
  .exchange (.tick 4) (.inr 2) (.exchange (.tick 2) (.inr 0) (.request (.tick 0)))

private theorem hasTrace_twoBackedges_iff (total : Bool) :
    HasTrace (sourceObservation instr (graph total) (sourceStore 4)) twoBackedges ↔ total = true := by
  rw [from_entry, twoBackedges, hasTrace_back_iff total false (sourceStore 4) 4 2 rfl (by cases total <;> decide),
    hasTrace_back_iff _ _ _ _ _ (nextOperand ..) (by cases total <;> decide),
    resume_at _ _ _ _ (nextOperand ..)]
  cases total
  · simpa only [Bool.false_or, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, iff_false,
      hasTrace_diverge_iff] using
      (show (Trace.request (.tick 0) : Trace Event (Transfer Atom)) ≠ .prefix from nofun)
  · simpa only [Bool.true_or, ↓reduceIte, iff_true] using
      hasTrace_vis_request (.tick 0) (continueTick true _ 0)

-- The reply 2 supplies the second request and the next reply 0 supplies the
-- third. Only the total opcode offers that third request.
private theorem packed_distinguishing_trace :
    HasTrace (packedObservation totalClosed instr (inputs 4).rightStore) twoBackedges ∧
      ¬ HasTrace (packedObservation partialClosed instr (inputs 4).leftStore) twoBackedges := by
  rw [packedObservation_eq_sourceObservation, packedObservation_eq_sourceObservation]
  change HasTrace (sourceObservation instr (graph true) (sourceStore 4)) twoBackedges ∧
    ¬ HasTrace (sourceObservation instr (graph false) (sourceStore 4)) twoBackedges
  simp only [hasTrace_twoBackedges_iff, true_and, Bool.false_eq_true, not_false_eq_true]

example : ¬ TraceLE (packedObservation totalClosed instr (inputs 4).rightStore)
    (packedObservation partialClosed instr (inputs 4).leftStore) :=
  fun reverse => packed_distinguishing_trace.2 (reverse twoBackedges packed_distinguishing_trace.1)

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.TraceExamples
