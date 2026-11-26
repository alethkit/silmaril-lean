module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Admission
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Correctness

/-! # Exact admission, simultaneous transfers and finite machine returns -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Activation Prog StepsNWithin step)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA (Inputs)

theorem lowerChecked_eq_some_iff (g : NativeGraph) (target : Prog Reg) :
    lowerChecked g = some target ↔ g = graph ∧ target = lower :=
  Proofs.lowerChecked_eq_some_iff g target

theorem lower_wellFormed : lowerFunc.WellFormed := by decide

theorem checked_wellFormed {g : NativeGraph} {target : Prog Reg} (ok : lowerChecked g = some target) :
    target.WellFormed := by
  obtain ⟨_, rfl⟩ := (lowerChecked_eq_some_iff g target).mp ok
  simpa [Prog.WellFormed, lower] using lower_wellFormed

theorem initial_bank (args : Inputs Word) :
    graph.initial model (input args) = bank args.first args.second 0 :=
  Proofs.initial_bank args

/-- Native feedback reads the two crossed operands and the incremented
index from one producer environment. -/
theorem feedback_bank (args : Inputs Word) (first second index : Word) :
    let ports := appendTuple (bank first second index) (input args)
    graph.latch model .backedge ports (graph.header.eval model ports PUnit.unit) =
      bank second first (index + 1) :=
  Proofs.feedback_bank args first second index

theorem incoming_operand (edge : Incoming) :
    ((lowerFunc.block? (incomingSlot edge).1).bind
      fun block => block.term.args[(incomingSlot edge).2]?) =
      some (1, incomingRegisters edge) :=
  Proofs.incoming_operand edge

/-- The actual entry terminator reads both payloads and the seed from the
predecessor frame and writes the bank. -/
theorem step_entry (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory) (first second : Word)
    (hf : fr.get (.arg 1) = some first) (hs : fr.get (.arg 2) = some second)
    (hi : fr.get (.pre 0) = some 0) :
    step lower ⟨⟨0, 0, preheader.ops.length⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr first second 0, stack, mem⟩ :=
  Proofs.step_entry fr stack mem first second hf hs hi

/-- The taken arm reads both old payloads before either destination is
written. Only the bank is rebound, with its payloads exchanged. -/
theorem step_feedback (fr : Frame Reg) (stack : List (Activation Reg)) (mem : Memory)
    (first second next guard : Word)
    (hf : fr.get .first = some first) (hs : fr.get .second = some second)
    (hi : fr.get (.node 1) = some next) (hc : fr.get (.node 0) = some guard) (taken : guard ≠ 0) :
    step lower ⟨⟨0, 1, header.ops.length⟩, fr, stack, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr second first next, stack, mem⟩ :=
  Proofs.step_feedback fr stack mem first second next guard hf hs hi hc taken

/-- Native execution reaches the unsigned word limit without wrapping the
latched index. The exit activation does not take a backedge. -/
theorem source_returns_at_limit (args : Inputs Word) :
    ∃ value : Word, graph.ReturnsAfter model (input args) args.limit.toNat
      (graph.initial model (input args)) value :=
  Proofs.source_returns_at_limit args

theorem lower_returns_iff {g : NativeGraph} {target : Prog Reg} (ok : lowerChecked g = some target)
    (args : Inputs Word) (initial final : Memory) (returned : List Word) :
    target.oracle 0 (wordArgs args) initial returned final ↔
      ∃ value : Word, g.Returns model (input args) value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨rfl, rfl⟩ := (lowerChecked_eq_some_iff g target).mp ok
  exact Proofs.lower_returns_iff args initial final returned

/-- The count includes three preheader steps and four per activation.
The terminal return follows the counted running steps. -/
theorem lower_stepsN_iff {g : NativeGraph} {target : Prog Reg} (ok : lowerChecked g = some target)
    (args : Inputs Word) (initial final : Memory) (returned : List Word) (running : Nat) :
    (∃ start finish, target.start 0 (wordArgs args) initial = some start ∧
      StepsNWithin target [] running start finish ∧ step target finish = .returned returned final) ↔
    ∃ (backedges : Nat) (value : Word), g.ReturnsAfter model (input args) backedges
      (g.initial model (input args)) value ∧ running = 4 * backedges + 7 ∧
        returned = [value] ∧ final = initial := by
  obtain ⟨rfl, rfl⟩ := (lowerChecked_eq_some_iff g target).mp ok
  exact Proofs.lower_stepsN_iff args initial final returned running

end Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank
