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
  simpa [Prog.WellFormed, Routes.lower, BankRoutes.lower, BankRoutes.lowerWith, BankRoutes.lowerWithRow] using wf

/-- Checked positions are preserved in the actual operands and return port. -/
theorem checkBankRoutes_registers {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {r : BankRoutes payloads} (ok : checkBankRoutes payloads entry feedback result = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg ∧ r.result.val = result :=
  Proofs.checkBankRoutes_registers ok

theorem lowerBankChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (target : Prog Reg) :
    lowerBankChecked payloads entry feedback result = some target ↔
      ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
        r.lowerFunc.WellFormed ∧ target = r.lower :=
  Proofs.lowerBankChecked_eq_some_iff payloads entry feedback result target

theorem lowerBankChecked_zero (entry feedback : List Nat) (result : Nat) :
    lowerBankChecked 0 entry feedback result = none := by
  simp [lowerBankChecked, checkBankRoutes]

theorem bank_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {target : Prog Reg} (ok : lowerBankChecked payloads entry feedback result = some target) :
    target.WellFormed := by
  obtain ⟨r, _, wf, rfl⟩ := (lowerBankChecked_eq_some_iff payloads entry feedback result target).mp ok
  simpa [Prog.WellFormed, BankRoutes.lower, BankRoutes.lowerWith, BankRoutes.lowerWithRow] using wf

/-- Admission recovers the checked update, copy routes, and the machine's
SSA well-formedness proof. -/
theorem lowerComputedChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (spec : FeedbackSpec) (target : Prog Reg) :
    lowerComputedChecked payloads entry feedback result spec = some target ↔
      ∃ update, spec.check payloads = some update ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWith (some update)).WellFormed ∧ target = r.lowerWith (some update) :=
  Proofs.lowerComputedChecked_eq_some_iff payloads entry feedback result spec target

theorem computed_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {spec : FeedbackSpec} {target : Prog Reg}
    (ok : lowerComputedChecked payloads entry feedback result spec = some target) :
    target.WellFormed := by
  obtain ⟨u, _, r, _, wf, rfl⟩ :=
    (lowerComputedChecked_eq_some_iff payloads entry feedback result spec target).mp ok
  change (r.lowerFuncWithRow [u]).WellFormed at wf
  simpa [Prog.WellFormed, BankRoutes.lowerWith, BankRoutes.lowerWithRow] using wf

section ComputedFeedback

variable {payloads : Nat} (r : BankRoutes payloads) (u : FeedbackUpdate payloads)

/-- The actual taken branch reads both the computed result and all copies
from the same producer frame before writing any payload register. -/
theorem computed_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWith (some u) fr old
    step (r.lowerWith (some u)) ⟨⟨0, 1, (r.headerWith (some u)).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWith (some u) input old), stk, mem⟩ :=
  Proofs.bank_step_feedback_with r [u] input old fr stk mem agree taken

/-- An actual machine header activation computes the word from the old
bank, then takes the branch selected by the independent native step. -/
theorem computed_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWith (some u)) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWith (some u)).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWith (some u) fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWith (some u) fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees_with r [u] input old fr mem agree

theorem computed_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWith (some u)).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWith (some u)).Returns model input value ∧
        returned = [value] ∧ final = initial :=
  Proofs.bank_returns_with_iff r [u] input initial final returned

end ComputedFeedback

theorem checkFeedbackRow_eq_some_iff (payloads : Nat) (specs : List FeedbackSpec)
    (updates : List (FeedbackUpdate payloads)) :
    checkFeedbackRow payloads specs = some updates ↔
      specs.mapM (fun spec => spec.check payloads) = some updates ∧
        (updates.map FeedbackUpdate.destination).Nodup :=
  Proofs.checkFeedbackRow_eq_some_iff payloads specs updates

theorem lowerFeedbackRowChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (specs : List FeedbackSpec) (target : Prog Reg) :
    lowerFeedbackRowChecked payloads entry feedback result specs = some target ↔
      ∃ updates, checkFeedbackRow payloads specs = some updates ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWithRow updates).WellFormed ∧ target = r.lowerWithRow updates :=
  Proofs.lowerFeedbackRowChecked_eq_some_iff payloads entry feedback result specs target

theorem row_checked_wellFormed {payloads : Nat} {entry feedback : List Nat} {result : Nat}
    {specs : List FeedbackSpec} {target : Prog Reg}
    (ok : lowerFeedbackRowChecked payloads entry feedback result specs = some target) :
    target.WellFormed := by
  obtain ⟨_, _, _, _, wf, rfl⟩ :=
    (lowerFeedbackRowChecked_eq_some_iff payloads entry feedback result specs target).mp ok
  simpa [Prog.WellFormed, BankRoutes.lowerWithRow] using wf

theorem lowerFeedbackRowChecked_nil (payloads : Nat) (entry feedback : List Nat) (result : Nat) :
    lowerFeedbackRowChecked payloads entry feedback result [] =
      lowerBankChecked payloads entry feedback result := rfl

theorem lowerFeedbackRowChecked_singleton (payloads : Nat) (entry feedback : List Nat) (result : Nat)
    (spec : FeedbackSpec) :
    lowerFeedbackRowChecked payloads entry feedback result [spec] =
      lowerComputedChecked payloads entry feedback result spec := rfl

section FeedbackRows

variable {payloads : Nat} (r : BankRoutes payloads) (updates : List (FeedbackUpdate payloads))

/-- The actual taken branch reads the computed results and all copies
from the same producer frame before writing any payload register. -/
theorem row_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (taken : counter old ≠ 0) :
    let after := headerFrameWithRow updates fr old
    step (r.lowerWithRow updates) ⟨⟨0, 1, (r.headerWithRow updates).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWithRow updates input old), stk, mem⟩ :=
  Proofs.bank_step_feedback_with r updates input old fr stk mem agree taken

/-- An actual machine header activation computes the row from the old
bank, then takes the branch selected by the independent native step. -/
theorem row_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWithRow updates) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWithRow updates).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWithRow updates fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWithRow updates fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees_with r updates input old fr mem agree

theorem row_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWithRow updates).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWithRow updates).Returns model input value ∧
        returned = [value] ∧ final = initial :=
  Proofs.bank_returns_with_iff r updates input initial final returned

end FeedbackRows

section ArbitraryArity

variable {payloads : Nat} (r : BankRoutes payloads)

theorem bank_incoming_operand (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) :=
  Proofs.bank_incoming_operand r edge

theorem bank_step_entry (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  Proofs.bank_step_entry r input fr stk mem agree

theorem bank_step_feedback (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ :=
  Proofs.bank_step_feedback r input old fr stk mem agree next test taken

/-- One native activation determines the exact successor of the emitted RTL
header, with the selected return or the simultaneous feedback bank. -/
theorem bank_header_agrees (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) :=
  Proofs.bank_header_agrees r input old fr mem agree

/-- Finite return preserves and reflects the selected word and whole memory. -/
theorem bank_returns_iff (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.bank_returns_iff r input initial final returned

end ArbitraryArity

variable (r : Routes)

theorem incoming_operand (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) :=
  Proofs.bank_incoming_operand r.toBankRoutes edge

theorem step_entry (input : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  Proofs.bank_step_entry r.toBankRoutes input fr stk mem agree

theorem step_feedback (input old : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ :=
  Proofs.bank_step_feedback r.toBankRoutes input old fr stk mem agree next test taken

/-- One independent native activation determines the exact RTL successor
state after the header's producer instructions and selected transfer. -/
theorem header_agrees (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (payloads := 3) (headerFrame fr old) next, [], mem⟩) :=
  Proofs.header_agrees r input old fr mem agree

theorem lower_returns_iff (input : WordTuple 4) (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.bank_returns_iff r.toBankRoutes input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing
