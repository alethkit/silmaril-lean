module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Frame
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy model word)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

variable {payloads : Nat}

private theorem word_arguments {args : List PortTy} {fr : Frame Reg}
    {input : Tuple (Val model.value) args}
    (h : ArgsMatch fr input) (wire : Origin args [] wordPort) :
    fr.get (register wire.address) = some (read model wire input PUnit.unit) := by
  cases wire with
  | arg p => exact h p
  | output i _ => exact i.elim0

private theorem extend_addresses {args users : List PortTy} (past : List (List PortTy))
    (wires : Wires args [] users) : (extendArguments past wires).addresses = wires.addresses := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      change (.arg p.index : Silmaril.SSA.RVSDG.Address) :: (extendArguments past rest).addresses =
        .arg p.index :: Wires.addresses rest
      rw [ih]
    | output i _ => exact i.elim0

private theorem feedback_registers (r : BankRoutes payloads) :
    r.incomingRegisters .backedge = .node 1 :: emitColumn r.feedback := by
  change .node 1 :: (extendArguments _ r.feedback).addresses.map register = _
  rw [extend_addresses]
  rfl

private theorem extend_read {args users : List PortTy} {past : List (List PortTy)}
    (wires : Wires args [] users) (input : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) :
    (extendArguments past wires).read input locals = wires.read input PUnit.unit := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      change Tuple.cons (input.get p) ((extendArguments past rest).read input locals) =
        Tuple.cons (input.get p) (Wires.read rest input PUnit.unit)
      rw [ih]
    | output i _ => exact i.elim0

theorem bank_incoming_operand (r : BankRoutes payloads) (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) := by
  cases edge <;> rfl

private theorem step_entry_with (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step (r.lowerWith update) ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr ((r.graphWith update).initial model input), stk, mem⟩ := by
  have reads := readColumn_eq (arity := payloads + 1) ((r.graphWith update).phiInputs .entry) input PUnit.unit fr (word_arguments agree)
  change transfer (r.lowerWith update) _ 1 (r.incomingWith update .entry) = _
  have target : (r.lowerWith update).block? 0 1 = some (r.headerWith update) := rfl
  have reads : fr.readAll (r.incomingWith update .entry) = some (words (n := payloads + 1) ((r.graphWith update).initial model input)) := reads
  have write : fr.writeAll (r.headerWith update).params (words (n := payloads + 1) ((r.graphWith update).initial model input)) =
    some (bindBank fr ((r.graphWith update).initial model input)) := bindWords_write (payloads + 1) fr _
  simp [transfer, reads, target, write]

theorem bank_step_entry (r : BankRoutes payloads) (input : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ :=
  step_entry_with r none input fr stk mem agree

private theorem counter_read (input old : WordTuple (payloads + 1)) :
    (appendTuple old input).get (counterPort payloads) = counter old :=
  suffix_get input old .head

private theorem return_read (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) :
    (appendTuple old input).get (suffixPort (wordPorts (payloads + 1)) r.resultPort) = r.returnWord old :=
  suffix_get input old r.resultPort

private theorem nextBank_eq (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) :
    r.nextBank input old =
      .cons (counter old - 1) (r.feedback.read (appendTuple old input) PUnit.unit) := by
  let joint := appendTuple old input
  change Tuple.cons (F := Val model.value) (t := wordPort)
      (BitVec.sub (joint.get (counterPort payloads)) (1 : Word))
      ((extendArguments _ r.feedback).read joint (r.graph.header.eval model joint PUnit.unit)) = _
  rw [counter_read input old, extend_read]
  rfl

private theorem test_zero (old : WordTuple (payloads + 1)) : testWord old = 0 ↔ counter old = 0 := by
  by_cases h : counter old = 0 <;> simp [testWord, ofBool, h]

private theorem header_term (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads)) :
    (r.headerWith update).term =
      .cond (.node 3) 1 (r.incomingWith update .backedge) 2 [register (r.graphWith update).result.address] := by
  cases update <;> rfl

private theorem feedback_from_reads (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (old nextBank : WordTuple (payloads + 1)) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (reads : fr.readAll (r.incomingWith update .backedge) = some (words nextBank))
    (test : fr.get (.node 3) = some (testWord old)) (taken : counter old ≠ 0) :
    step (r.lowerWith update) ⟨⟨0, 1, (r.headerWith update).ops.length⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr nextBank, stk, mem⟩ := by
  have fetch := Prog.fetch_term (p := r.lowerWith update) (f := 0) (l := 1) (b := r.headerWith update) rfl
  have target : (r.lowerWith update).block? 0 1 = some (r.headerWith update) := rfl
  have write : fr.writeAll (r.headerWith update).params (words nextBank) =
    some (bindBank fr nextBank) := bindWords_write (payloads + 1) fr _
  have nonzero := mt (test_zero old).mp taken
  simp only [step, fetch, header_term, test]
  change transfer (r.lowerWith update) _
    (if testWord old = 0 then 2 else 1)
    (if testWord old = 0 then [register (r.graphWith update).result.address]
      else r.incomingWith update .backedge) = _
  rw [ite_eq_right nonzero, ite_eq_right nonzero]
  simp [transfer, target, reads, write]

theorem bank_step_feedback (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ := by
  have payload := readColumn_eq r.feedback (appendTuple old input) PUnit.unit fr (word_arguments agree)
  have reads : fr.readAll (r.incomingRegisters .backedge) = some (words (r.nextBank input old)) := by
    rw [feedback_registers, nextBank_eq]
    simp only [Frame.readAll, List.mapM_cons, next]
    unfold Frame.readAll at payload
    rw [payload]
    rfl
  exact feedback_from_reads r none old _ fr stk mem reads test taken

private theorem source_step (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) :
    (r.graphWith update).step model input old =
      if counter old = 0 then .inl (r.returnWord old) else .inr (r.nextBankWith update input old) := by
  let joint := appendTuple old input
  cases update <;>
    (change (if (!(BEq.beq (α := Word) (joint.get (counterPort payloads)) 0)) = true
        then Sum.inr (α := Word) _
        else Sum.inl ((joint.get (suffixPort (wordPorts (payloads + 1)) r.resultPort)) : Word)) = _
     rw [counter_read input old, return_read r input old]
     by_cases h : counter old = 0 <;> (simp [h]; rfl))

private theorem get_counter {fr : Frame Reg} {input old : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr (appendTuple old input)) :
    fr.get (.arg (counterPort payloads).index) = some (counter old) := by
  have got := agree (counterPort payloads)
  rw [counter_read] at got
  exact got

private theorem get_return (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    {fr : Frame Reg} {input old : WordTuple (payloads + 1)} (agree : ArgsMatch fr (appendTuple old input)) :
    fr.get (register (r.graphWith update).result.address) = some (r.returnWord old) := by
  change fr.get (.arg (suffixPort (wordPorts (payloads + 1)) r.resultPort).index) = _
  have got := agree (suffixPort (wordPorts (payloads + 1)) r.resultPort)
  rw [return_read r] at got
  exact got

private theorem payload_read (input old : WordTuple (payloads + 1)) (p : Fin payloads) :
    (appendTuple old input).get (oldPayloadPort payloads p) = old.get (payloadPort payloads p) :=
  suffix_get input old _

private theorem header_matches (update : Option (FeedbackUpdate payloads))
    {fr : Frame Reg} {input old : WordTuple (payloads + 1)}
    (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (headerFrameWith update fr old) (appendTuple old input) := by
  intro p
  cases update <;> simpa [headerFrameWith, headerFrame] using agree p

private def atPoint (label pc : Nat) (fr : Frame Reg) (mem : Memory) : State Reg :=
  ⟨⟨0, label, pc⟩, fr, [], mem⟩

private theorem next_counter (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) :
    counter (r.nextBankWith update input old) = counter old - 1 := by
  let joint := appendTuple old input
  cases update <;>
    (change BitVec.sub (joint.get (counterPort payloads)) (1 : Word) = _
     rw [counter_read input old]
     rfl)

private theorem feedback_op_eval (op : FeedbackOp) (x y : Word) :
    op.target.eval x y = some (op.eval x y) := by
  cases op <;> rfl

private theorem feedback_fetch (r : BankRoutes payloads) (u : FeedbackUpdate payloads)
    (fr : Frame Reg) (mem : Memory) :
    (r.lowerWith (some u)).fetch (atPoint 1 4 fr mem).point =
      some (.op (.binary u.operation.target (.node 4) (.arg (oldPayloadPort payloads u.left).index)
        (.arg (oldPayloadPort payloads u.right).index))) := by
  rcases u with ⟨op, destination, left, right⟩
  cases op <;> rfl

private theorem header_read_test (update : Option (FeedbackUpdate payloads))
    (fr : Frame Reg) (old : WordTuple (payloads + 1)) :
    (headerFrameWith update fr old).get (.node 3) = some (testWord old) := by
  cases update <;> rfl

private theorem header_word_reads (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input))
    (wire : Origin (wordPorts (payloads + 1) ++ wordPorts (payloads + 1))
      (extend [] (headerSigsWith update)) wordPort) :
    (headerFrameWith update fr old).get (register wire.address) =
      some (read model wire (appendTuple old input)
        ((r.graphWith update).header.eval model (appendTuple old input) PUnit.unit)) := by
  cases wire with
  | arg p => exact header_matches update agree p
  | output i p =>
    cases update with
    | none =>
      fin_cases i <;> cases p <;> try (rename_i port; exact nomatch port)
      · rfl
      · change some (counter old - 1) = some (BitVec.sub ((appendTuple old input).get (counterPort payloads)) 1)
        rw [counter_read]
        rfl
      · rfl
    | some u =>
      fin_cases i <;> cases p <;> try (rename_i port; exact nomatch port)
      · rfl
      · change some (counter old - 1) = some (BitVec.sub ((appendTuple old input).get (counterPort payloads)) 1)
        rw [counter_read]
        rfl
      · rfl
      · change some (u.eval old) = some (model.run u.operation.source
          (.cons ((appendTuple old input).get (oldPayloadPort payloads u.left))
            (.cons ((appendTuple old input).get (oldPayloadPort payloads u.right)) .nil)))
        rw [payload_read, payload_read]
        rcases u with ⟨op, _, _, _⟩
        cases op <;> rfl

private theorem header_column_reads (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    (headerFrameWith update fr old).readAll (r.incomingWith update .backedge) =
      some (words (r.nextBankWith update input old)) :=
  readColumn_eq (arity := payloads + 1) ((r.graphWith update).phiInputs .backedge)
    (appendTuple old input) ((r.graphWith update).header.eval model (appendTuple old input) PUnit.unit)
    (headerFrameWith update fr old) (header_word_reads r update input old fr agree)

theorem bank_step_feedback_with (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg) (stk : List (Activation Reg)) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple old input)) (taken : counter old ≠ 0) :
    let after := headerFrameWith update fr old
    step (r.lowerWith update) ⟨⟨0, 1, (r.headerWith update).ops.length⟩, after, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank after (r.nextBankWith update input old), stk, mem⟩ :=
  feedback_from_reads r update old _ _ stk mem (header_column_reads r update input old fr agree)
    (header_read_test update fr old) taken

/-- Run the four countdown instructions and the optional feedback producer. -/
private theorem header_prefix (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) {finish : State Reg}
    (tail : Steps (r.lowerWith update)
      (atPoint 1 (r.headerWith update).ops.length (headerFrameWith update fr old) mem) finish) :
    Steps (r.lowerWith update) (atPoint 1 0 fr mem) finish := by
  let one := fr.set (.node 0) 1
  let decremented := one.set (.node 1) (counter old - 1)
  let withZero := decremented.set (.node 2) 0
  have readCounter : fr.get (.arg (counterPort payloads).index) = some (counter old) := get_counter agree
  have subExec : (Op.binary .sub (.node 1) (.arg (counterPort payloads).index) (.node 0)).exec one mem = some (decremented, mem) := by
    have read : one.get (.arg (counterPort payloads).index) = some (counter old) := by simpa [one] using readCounter
    have literal : one.get (.node 0) = some 1 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have testExec : (Op.binary (.cmp .ne) (.node 3) (.arg (counterPort payloads).index) (.node 2)).exec withZero mem =
      some (headerFrame fr old, mem) := by
    have read : withZero.get (.arg (counterPort payloads).index) = some (counter old) := by
      simpa [withZero, decremented, one] using readCounter
    have literal : withZero.get (.node 2) = some 0 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have s₀ := Transition.op (p := r.lowerWith update) (s := atPoint 1 0 fr mem)
    (o := .const (.node 0) 1) rfl (rfl : _ = some (one, mem))
  have s₁ := Transition.op (p := r.lowerWith update) (s := atPoint 1 1 one mem) rfl subExec
  have s₂ := Transition.op (p := r.lowerWith update) (s := atPoint 1 2 decremented mem)
    (o := .const (.node 2) 0) rfl (rfl : _ = some (withZero, mem))
  have s₃ := Transition.op (p := r.lowerWith update) (s := atPoint 1 3 withZero mem) rfl testExec
  have scheduled : Steps (r.lowerWith update) (atPoint 1 0 fr mem) (atPoint 1 4 (headerFrame fr old) mem) :=
    .head s₀.step_eq (.head s₁.step_eq (.head s₂.step_eq (.head s₃.step_eq .refl)))
  cases update with
  | none => exact scheduled.trans tail
  | some u =>
    let after := headerFrame fr old
    let left := (oldPayloadPort payloads u.left).index
    let right := (oldPayloadPort payloads u.right).index
    have leftRead : after.get (.arg left) = some (old.get (payloadPort payloads u.left)) := by
      have got := header_matches none agree (oldPayloadPort payloads u.left)
      rw [payload_read] at got
      exact got
    have rightRead : after.get (.arg right) = some (old.get (payloadPort payloads u.right)) := by
      have got := header_matches none agree (oldPayloadPort payloads u.right)
      rw [payload_read] at got
      exact got
    have exec : (Op.binary u.operation.target (.node 4) (.arg left) (.arg right)).exec after mem =
        some ((headerFrame fr old).set (.node 4) (u.eval old), mem) := by
      simp only [Op.exec, leftRead, rightRead, feedback_op_eval, Option.map_some]
      rfl
    exact scheduled.trans (.head
      (Transition.op (s := atPoint 1 4 after mem) (feedback_fetch r u after mem) exec).step_eq tail)

private theorem exit_step (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (fr : Frame Reg) (mem : Memory) (value : Word)
    (read : fr.get (register (r.graphWith update).result.address) = some value) (halt : fr.get (.node 3) = some 0) :
    step (r.lowerWith update) (atPoint 1 (r.headerWith update).ops.length fr mem) =
      .running (atPoint 2 0 (fr.set .phi value) mem) := by
  have fetch := Prog.fetch_term (p := r.lowerWith update) (f := 0) (l := 1) (b := r.headerWith update) rfl
  have target : (r.lowerWith update).block? 0 2 = some exitBlock := rfl
  simp [step, fetch, header_term, halt, transfer, Frame.readAll, target, read, atPoint, exitBlock, Frame.writeAll]

theorem bank_header_agrees_with (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (r.lowerWith update) ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match (r.graphWith update).step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrameWith update fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrameWith update fr old) next, [], mem⟩) := by
  rw [source_step]
  let after := headerFrameWith update fr old
  have afterAgrees := header_matches update agree
  by_cases halt : counter old = 0
  · simp only [ite_eq_left halt]
    have read : after.get (register (r.graphWith update).result.address) = some (r.returnWord old) := get_return r update afterAgrees
    have guard : after.get (.node 3) = some 0 := by
      have test : after.get (.node 3) = some (testWord old) := header_read_test update fr old
      rw [(test_zero old).mpr halt] at test
      exact test
    exact header_prefix r update input old fr mem agree (.head (exit_step r update after mem _ read guard) .refl)
  · simp only [ite_eq_right halt]
    exact header_prefix r update input old fr mem agree
      (.head (bank_step_feedback_with r update input old fr [] mem agree halt) .refl)

private theorem header_returns (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (mem : Memory)
    {count : Nat} {old : WordTuple (payloads + 1)} {value : sortValue model.value word}
    (source : (r.graphWith update).ReturnsAfter model input count old value) :
    ∀ fr : Frame Reg, ArgsMatch fr (appendTuple old input) →
      Behaves (r.lowerWith update) (atPoint 1 0 fr mem) (.returned [value] mem) := by
  refine Graph.ReturnsAfter.rec (g := (r.graphWith update)) (m := model) (input := input)
    (motive := fun _ old value _ => ∀ fr, ArgsMatch fr (appendTuple old input) →
      Behaves (r.lowerWith update) (atPoint 1 0 fr mem) (.returned [value] mem)) ?_ ?_ source
  · intro old value taken fr agree
    have activation := bank_header_agrees_with r update input old fr mem agree
    rw [taken] at activation
    exact ⟨atPoint 2 0 ((headerFrameWith update fr old).set .phi value) mem, activation, rfl⟩
  · intro _ old next value taken _ ih fr agree
    have activation := bank_header_agrees_with r update input old fr mem agree
    rw [taken] at activation
    have afterAgrees := header_matches update agree
    obtain ⟨finish, suffix, observed⟩ := ih (bindBank (headerFrameWith update fr old) next)
      (bank_matches (input_matches afterAgrees) next)
    exact ⟨finish, activation.trans suffix, observed⟩

private theorem source_total (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads)) (input old : WordTuple (payloads + 1)) :
    ∃ value : Word, (r.graphWith update).ReturnsAfter model input (counter old).toNat old value := by
  generalize measure : (counter old).toNat = count
  induction count generalizing old with
  | zero =>
    have halt : counter old = 0 := BitVec.eq_of_toNat_eq measure
    exact ⟨r.returnWord old, .exit ((source_step r update input old).trans (ite_eq_left halt))⟩
  | succ count ih =>
    have more : counter old ≠ 0 := by
      intro halt
      rw [halt] at measure
      cases measure
    have positive : (1 : Word) ≤ counter old := by
      rw [BitVec.le_def]
      change 1 ≤ (counter old).toNat
      omega
    have dec : (counter (r.nextBankWith update input old)).toNat = count := by
      have eq := next_counter r update input old
      rw [eq, BitVec.toNat_sub_of_le positive]
      change (counter old).toNat - 1 = count
      omega
    obtain ⟨value, rest⟩ := ih (r.nextBankWith update input old) dec
    exact ⟨value, .backedge ((source_step r update input old).trans (ite_eq_right more)) rest⟩

private theorem source_to_oracle (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (mem : Memory) (value : Word)
    (source : (r.graphWith update).Returns model input value) : (r.lowerWith update).oracle 0 (words input) mem [value] mem := by
  let fr := bindWords 0 Frame.empty input
  have agree : ArgsMatch fr input := by
    intro p
    simpa only [Nat.zero_add] using bindWords_get 0 Frame.empty input p
  let initial := (r.graphWith update).initial model input
  obtain ⟨_, run⟩ := source
  obtain ⟨finish, suffix, observed⟩ := header_returns r update input mem run
    (bindBank fr initial) (bank_matches agree initial)
  have start : (r.lowerWith update).start 0 (words input) mem = some (atPoint 0 0 fr mem) := by
    change ((Frame.empty.writeAll (paramRegs 0 (payloads + 1)) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
        (fun entered => (⟨entered.1, entered.2, [], mem⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  exact ⟨atPoint 0 0 fr mem, start, finish, .head (step_entry_with r update _ fr [] mem agree) suffix, observed⟩

theorem bank_returns_with_iff (r : BankRoutes payloads) (update : Option (FeedbackUpdate payloads))
    (input : WordTuple (payloads + 1)) (initial final : Memory)
    (returned : List Word) :
    (r.lowerWith update).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (r.graphWith update).Returns model input value ∧ returned = [value] ∧ final = initial := by
  constructor
  · intro actual
    obtain ⟨value, run⟩ := source_total r update input ((r.graphWith update).initial model input)
    have source : (r.graphWith update).Returns model input value := ⟨_, run⟩
    have expected := source_to_oracle r update input initial value source
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic (r.lowerWith update) 0 (words input) initial _ _ _ _ actual expected
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, source, rfl, memEq⟩
    subst final
    exact source_to_oracle r update input initial value source

theorem bank_header_agrees (r : BankRoutes payloads) (input old : WordTuple (payloads + 1)) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) := by
  have follows := bank_header_agrees_with r none input old fr mem agree
  cases result : r.graph.step model input old <;>
    (have evaluated : (r.graphWith none).step model input old = _ := result
     rw [evaluated] at follows
     exact follows)

theorem bank_returns_iff (r : BankRoutes payloads) (input : WordTuple (payloads + 1))
    (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial :=
  bank_returns_with_iff r none input initial final returned

theorem lowerComputedChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (spec : FeedbackSpec) (target : Prog Reg) :
    lowerComputedChecked payloads entry feedback result spec = some target ↔
      ∃ update, spec.check payloads = some update ∧
        ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
          (r.lowerFuncWith (some update)).WellFormed ∧ target = r.lowerWith (some update) := by
  simp only [lowerComputedChecked, Option.bind_eq_some_iff]
  exact exists_congr (fun update => and_congr_right (fun _ =>
    exists_congr (fun r => and_congr_right (fun _ => by
      by_cases wf : (r.lowerFuncWith (some update)).WellFormed <;> simp [wf, eq_comm]))))

private theorem cast_addresses {args newArgs users : List PortTy} (same : args = newArgs)
    (wires : Wires args [] users) :
    (same ▸ wires : Wires newArgs [] users).addresses = wires.addresses := by
  cases same
  rfl

theorem checkBankRoutes_registers {entry feedback : List Nat} {result : Nat} {r : BankRoutes payloads}
    (ok : checkBankRoutes payloads entry feedback result = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg ∧ r.result.val = result := by
  unfold checkBankRoutes at ok
  split at ok
  · rename_i valid
    cases initial : checkColumn (payloads + 1) payloads entry with
    | none => rw [initial] at ok; cases ok
    | some entryColumn =>
      rw [initial] at ok
      let size := payloads + 1
      let toHeader := wordPorts_append size size
      change (checkColumn (size + size) payloads feedback).map
        (fun next => BankRoutes.mk entryColumn (toHeader ▸ next) ⟨result, valid⟩) = _ at ok
      cases next : checkColumn (size + size) payloads feedback with
      | none => rw [next] at ok; cases ok
      | some feedbackColumn =>
        rw [next] at ok
        obtain rfl := Option.some.inj ok
        refine ⟨?_, ?_, rfl⟩
        · change .arg 0 :: emitColumn entryColumn = _
          rw [checkColumn_registers initial]
        · rw [feedback_registers]
          change .node 1 :: (toHeader ▸ feedbackColumn :
            Wires (wordPorts size ++ wordPorts size) [] (wordPorts payloads)).addresses.map register = _
          rw [cast_addresses]
          exact congrArg (List.cons (.node 1)) (checkColumn_registers next)
  · cases ok

theorem lowerBankChecked_eq_some_iff (payloads : Nat) (entry feedback : List Nat)
    (result : Nat) (target : Prog Reg) :
    lowerBankChecked payloads entry feedback result = some target ↔
      ∃ r, checkBankRoutes payloads entry feedback result = some r ∧
        r.lowerFunc.WellFormed ∧ target = r.lower := by
  rw [lowerBankChecked, Option.bind_eq_some_iff]
  exact exists_congr (fun r => and_congr_right (fun _ => by
    by_cases wf : r.lowerFunc.WellFormed <;> simp [wf, eq_comm]))

theorem header_agrees (r : Routes) (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (payloads := 3) (headerFrame fr old) next, [], mem⟩) := by
  have follows := bank_header_agrees r.toBankRoutes input old fr mem agree
  cases result : r.graph.step model input old <;>
    (have evaluated : r.toBankRoutes.graph.step model input old = _ := result
     rw [evaluated] at follows
     exact follows)

theorem checkRoutes_registers {entry feedback : List Nat} {r : Routes}
    (ok : checkRoutes entry feedback = some r) :
    r.incomingRegisters .entry = .arg 0 :: entry.map Reg.arg ∧
      r.incomingRegisters .backedge = .node 1 :: feedback.map Reg.arg := by
  unfold checkRoutes at ok
  cases initial : checkColumn 4 3 entry with
  | none => rw [initial] at ok; cases ok
  | some entryColumn =>
    rw [initial] at ok
    change (checkColumn 8 3 feedback).map (fun next => Routes.mk entryColumn next) = _ at ok
    cases next : checkColumn 8 3 feedback with
    | none => rw [next] at ok; cases ok
    | some feedbackColumn =>
      rw [next] at ok
      obtain rfl := Option.some.inj ok
      refine ⟨?_, ?_⟩
      · change .arg 0 :: emitColumn entryColumn = _
        rw [checkColumn_registers initial]
      · change (Routes.toBankRoutes ⟨entryColumn, feedbackColumn⟩).incomingRegisters .backedge = _
        rw [feedback_registers]
        change .node 1 :: emitColumn feedbackColumn = _
        rw [checkColumn_registers next]

theorem lowerChecked_eq_some_iff (entry feedback : List Nat) (target : Prog Reg) :
    lowerChecked entry feedback = some target ↔
      ∃ r, checkRoutes entry feedback = some r ∧ r.lowerFunc.WellFormed ∧ target = r.lower := by
  cases check : checkRoutes entry feedback with
  | none => simp [lowerChecked, check]
  | some route =>
    rw [lowerChecked, check]
    change (if route.lowerFunc.WellFormed then some route.lower else none) = some target ↔ _
    by_cases wf : route.lowerFunc.WellFormed <;> simp [wf, eq_comm]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
