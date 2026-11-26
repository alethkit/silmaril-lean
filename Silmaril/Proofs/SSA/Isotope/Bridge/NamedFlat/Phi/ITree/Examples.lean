module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Thms
import Silmaril.Semantics.ITree.Thms

/-! A visible request supplies the operand of the next visit to a φ header. -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Interaction.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending br ret)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree vis vis_bind iterate_fixpoint)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region)
open LambdaSSA.FiniteCFG (packedExecutionRegion packedTreeOutput)
open LetCase.LocallyNameless (Tm HasType)

private abbrev Reg := ULift.{1} Nat
private abbrev Key := ULift.{1} Unit
private abbrev Atom := ULift.{1} Nat
private abbrev SortName := ULift.{1} Unit

private def atom (n : Nat) : Value Atom := .atom ⟨n⟩

private inductive Opcode
  | tick
  | readCaptures

private inductive Event : Type → Type
  | tick (argument : Nat) : Event (Nat ⊕ Nat)
  | capture : Event Nat

private def num : Ty SortName := .base ⟨()⟩
private def captureTypes : BoundCtx (Ty SortName) 1 := .snoc .nil num
private def captureType : Ty SortName := LambdaSSA.Region.packedInputType captureTypes.toList
private def headerType : Ty SortName := .product (.product num .unit) (.product num .unit)

private instance : HasTy Opcode (Ty SortName) where
  src
    | .tick => num
    | .readCaptures => .unit
  trg
    | .tick => .coprod num num
    | .readCaptures => captureType

private def instr : Primitive Event Opcode Atom
  | .tick, .atom argument => vis (.tick argument.down) fun
      | .inl answer => pure (.inl (atom answer))
      | .inr answer => pure (.inr (atom answer))
  | .readCaptures, .unit => vis .capture (fun answer => pure (.pair .unit (atom answer)))
  | _, _ => Silmaril.Elgot.ITree.diverge

private def seedName : Reg := ⟨0⟩
private def phiName : Reg := ⟨1⟩
private def doneName : Reg := ⟨2⟩
private def backName : Reg := ⟨3⟩
private def header : Key := ⟨()⟩

-- The right payload is defined on the self-edge before the next φ entry.
private def graph : Graph Reg Key Opcode :=
  ⟨.term (br header),
    [(header, ⟨[⟨phiName, [(none, .var seedName), (some header, .var backName)]⟩],
      .term (.case (.app .tick (.var phiName)) doneName (ret (.var doneName)) backName (br header))⟩)]⟩

private def certificate : CFG.Cyclic.Phi.GlobalSSA.Certificate Reg Key := [(header, [])]
private def names : Fin 1 → Option Reg := fun _ => some seedName

private def admitted := (Certified.admit graph [seedName] certificate names captureTypes
  (fun _ => headerType) (fun _ => num)).get (by decide)

-- The same graph and valid SSA certificate still need a matching target profile.
example : (Certified.admit graph [seedName] certificate names captureTypes
    (fun _ => headerType) (fun _ => .unit)).isNone := by decide

example : (Certified.admit graph [] certificate names captureTypes
    (fun _ => headerType) (fun _ => num)).isNone := by decide

private def packetRead : Tm Empty Opcode 0 := .op .readCaptures .unit

private def closed := (admitted.close packetRead
  (show HasType Opcode .nil .nil packetRead captureType from .op .unit)).get (by decide)

private def sourceStore (seed : Nat) : Reg → Value Atom := fun _ => atom seed
private def ambient : Env Atom := fun _ => .unit
private def produce : Tree Event Atom := vis .capture (fun answer => pure ⟨answer⟩)

private theorem capture_packet :
    LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase packetRead) =
      (produce >>= fun reply => pure (Capture.packEnv 1 (Certified.captureEnv names (sourceStore reply.down)))) := by
  change LambdaSSA.Semantics.Interaction.term instr ambient (.op .readCaptures .unit) = _
  simp only [LambdaSSA.Semantics.Interaction.term, instr, pure_bind, produce, vis_bind,
    Capture.packEnv]
  rfl

private def pending (back : Bool) (store : Reg → Value Atom) : Pending Reg Key (Value Atom) :=
  (.jump (if back then some header else none) header, store)

private def afterBack (store : Reg → Value Atom) (operand reply : Nat) : Reg → Value Atom :=
  upd (upd store phiName (atom operand)) backName (atom reply)

private def afterTick (store : Reg → Value Atom) (operand : Nat) :
    Nat ⊕ Nat → Pending Reg Key (Value Atom)
  | .inl reply => (.returned (atom reply), upd (upd store phiName (atom operand)) doneName (atom reply))
  | .inr reply => pending true (afterBack store operand reply)

private def sourceStep := CFG.Cyclic.Phi.step (treeModel instr) graph

private theorem tick_step (back : Bool) (store : Reg → Value Atom) (argument : Nat)
    (reads : store (if back then backName else seedName) = atom argument) :
    sourceStep (pending back store) =
      vis (.tick argument) (fun reply => pure (.inr (afterTick store argument reply))) := by
  cases back <;>
    simp [seedName, backName] at reads <;>
    simp [sourceStep, pending, CFG.Cyclic.Phi.step, CFG.Cyclic.Phi.execute, CFG.Cyclic.Phi.assign,
      CFG.Cyclic.Phi.Row.operand, graph, List.lookup, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval,
      treeModel, instr, atom, br, ret, afterTick, afterBack, upd, reads, seedName, backName, phiName,
      ← bind_pure_comp, bind_assoc, vis_bind]
  all_goals
    funext reply
    cases reply <;> simp only [pure_bind]

private noncomputable def resume (transfer : Pending Reg Key (Value Atom)) : Tree Event (Transfer Atom) :=
  iter sourceStep transfer >>= fun p => pure (packedTreeOutput (treeExitNumber [none] p))

private theorem resume_return (store : Reg → Value Atom) (result : Nat) :
    resume (.returned (atom result), store) = pure (0, .inl (atom result)) := by
  unfold resume
  rw [congrFun (iterate_fixpoint sourceStep) (.returned (atom result), store)]
  simp only [sourceStep, CFG.Cyclic.Phi.step, pure_bind, Sum.elim_inl]
  rfl

private theorem resume_tick (back : Bool) (store : Reg → Value Atom) (argument : Nat)
    (reads : store (if back then backName else seedName) = atom argument) :
    resume (pending back store) =
      vis (.tick argument) (fun
        | .inl result => pure (0, .inl (atom result))
        | .inr reply => resume (pending true (afterBack store argument reply))) := by
  unfold resume
  rw [congrFun (iterate_fixpoint sourceStep) (pending back store), tick_step back store argument reads]
  simp only [vis_bind, pure_bind, Sum.elim_inr]
  congr 1
  funext reply
  cases reply with
  | inl result => exact resume_return _ result
  | inr reply => rfl

private theorem from_entry (seed : Nat) :
    (runTree instr graph (sourceStore seed) >>= fun p => pure (packedTreeOutput (treeExitNumber [none] p))) =
      resume (pending false (sourceStore seed)) := by
  have entered : CFG.Cyclic.Phi.execute (treeModel instr) none graph.entry (sourceStore seed) =
      pure (pending false (sourceStore seed)) := rfl
  rw [runTree, CFG.Cyclic.Phi.run, entered, pure_bind]
  rfl

private theorem packed_fixture :
    region instr ambient (packedExecutionRegion closed.typed) =
      vis .capture (fun seed => resume (pending false (sourceStore seed))) := by
  have compared := Certified.packed_run_tree closed instr produce
    (fun seed => sourceStore seed.down) ambient capture_packet
  simp only [produce, vis_bind, pure_bind, from_entry] at compared
  exact compared

-- The first continuing reply is the next visible argument. Either request can
-- return, and the dispatcher tags only that final result.
example : region instr ambient (packedExecutionRegion closed.typed) =
    vis .capture (fun seed =>
      vis (.tick seed) (fun
        | .inl result => pure (0, .inl (atom result))
        | .inr first =>
            vis (.tick first) (fun
              | .inl result => pure (0, .inl (atom result))
              | .inr second =>
                  resume (pending true (afterBack (afterBack (sourceStore seed) seed first) first second))))) := by
  rw [packed_fixture]
  congr 1
  funext seed
  rw [resume_tick false (sourceStore seed) seed rfl]
  congr 1
  funext first
  cases first with
  | inl result => rfl
  | inr reply => exact resume_tick true _ reply (by simp [afterBack, upd])

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Interaction.Examples
