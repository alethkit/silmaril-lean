module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution

/-! # Exact typed column emission and routed-loop execution -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Activation Block Label Prog State Steps step transfer)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read)
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

theorem checkColumn_registers {scope arity : Nat} {indices : List Nat}
    {wires : ArgumentColumn scope arity} (ok : checkColumn scope arity indices = some wires) :
    emitColumn wires = indices.map Reg.arg :=
  Proofs.checkColumn_registers ok

/-- Resolve every operand in the predecessor frame before binding any
destination. This law is independent of the number of word slots. -/
theorem readColumn_eq {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (fr : Frame Reg)
    (agree : ∀ wire : Origin args past wordPort,
      fr.get (register wire.address) = some (read model wire input locals)) :
    fr.readAll (emitColumn wires) = some (words (wires.read input locals)) :=
  Proofs.readColumn_eq wires input locals fr agree

/-- Matching native reads and a target of the declared arity give the exact
machine transfer, including the old stack and the entire memory. -/
theorem transfer_column {args : List PortTy} {past : List (List PortTy)} {arity : Nat}
    (wires : Wires args past (wordPorts arity)) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) (p : Prog Reg) (s : State Reg)
    (target : Label) (block : Block Reg) (found : p.block? s.point.func target = some block)
    (arityEq : block.params.length = arity)
    (agree : ∀ wire : Origin args past wordPort,
      s.frame.get (register wire.address) = some (read model wire input locals)) :
    ∃ after, s.frame.writeAll block.params (words (wires.read input locals)) = some after ∧
      transfer p s target (emitColumn wires) =
        .running ⟨⟨s.point.func, target, 0⟩, after, s.stack, s.mem⟩ :=
  Proofs.transfer_column wires input locals p s target block found arityEq agree

/-- The decoded positions become exactly the emitted register operands, in
slot order, beside the fixed incoming counter operand. -/
theorem checkRoutes_registers {entry feedback : List Nat} {r : Routes}
    (ok : checkRoutes entry feedback = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg :=
  Proofs.checkRoutes_registers ok

theorem lowerChecked_eq_some_iff (entry feedback : List Nat) (target : Prog Reg) :
    lowerChecked entry feedback = some target ↔
      ∃ r, checkRoutes entry feedback = some r ∧ r.lowerFunc.WellFormed ∧ target = r.lower :=
  Proofs.lowerChecked_eq_some_iff entry feedback target

theorem checked_wellFormed {entry feedback : List Nat} {target : Prog Reg}
    (ok : lowerChecked entry feedback = some target) : target.WellFormed := by
  obtain ⟨r, _, wf, rfl⟩ := (lowerChecked_eq_some_iff entry feedback target).mp ok
  simpa [Prog.WellFormed, Routes.lower] using wf

variable (r : Routes)

theorem incoming_operand (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) :=
  Proofs.incoming_operand r edge

theorem step_entry (input : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  Proofs.step_entry r input fr stk mem agree

theorem step_feedback (input old : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ :=
  Proofs.step_feedback r input old fr stk mem agree next test taken

/-- One independent native activation determines the exact RTL successor
state after the header's producer instructions and selected transfer. -/
theorem header_agrees (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) :=
  Proofs.header_agrees r input old fr mem agree

theorem lower_returns_iff (input : WordTuple 4) (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.lower_returns_iff r input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
