module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs

open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg PortTy model word)
open Silmaril.SSA.SeaOfNodes.Diamond (Val read sortValue)
open Silmaril.SSA.SeaOfNodes.Loop (Graph Incoming appendTuple)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)

private theorem tuple_pack (values : WordTuple 4) :
    ∃ c a b d : Word, values = pack c a b d := by
  cases values with
  | cons c rest =>
    cases rest with
    | cons a rest =>
      cases rest with
      | cons b rest =>
        cases rest with
        | cons d rest =>
          cases rest
          exact ⟨c, a, b, d, rfl⟩

private theorem bank_write (fr : Frame Reg) (values : WordTuple 4) :
    fr.writeAll bankParams (words values) = some (bindBank fr values) := by
  obtain ⟨_, _, _, _, rfl⟩ := tuple_pack values
  rfl

private theorem word_arguments {scope : Nat} {fr : Frame Reg} {input : WordTuple scope}
    (h : ArgsMatch fr input) (wire : Origin (wordPorts scope) [] wordPort) :
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

private theorem feedback_registers (r : Routes) :
    r.incomingRegisters .backedge = .node 1 :: emitColumn r.feedback := by
  change .node 1 :: (extendArguments _ r.feedback).addresses.map register = _
  rw [extend_addresses]
  rfl

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
      · rw [feedback_registers, checkColumn_registers next]

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

theorem incoming_operand (r : Routes) (edge : Incoming) :
    ((r.lowerFunc.block? (edge.select 0 1)).bind fun block => block.term.args[0]?) =
      some (1, r.incomingRegisters edge) := by
  cases edge <;> rfl

theorem step_entry (r : Routes) (input : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr input) :
    step r.lower ⟨⟨0, 0, 0⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.graph.initial model input), stk, mem⟩ := by
  have reads := readColumn_eq (arity := 4) (r.graph.phiInputs .entry) input PUnit.unit fr (word_arguments agree)
  change transfer r.lower _ 1 (r.incomingRegisters .entry) = _
  have target : r.lower.block? 0 1 = some r.header := rfl
  have reads : fr.readAll (r.incomingRegisters .entry) = some (words (n := 4) (r.graph.initial model input)) := reads
  have write : fr.writeAll r.header.params (words (n := 4) (r.graph.initial model input)) =
    some (bindBank fr (r.graph.initial model input)) := bank_write fr _
  simp [transfer, reads, target, write]

private theorem nextBank_eq (r : Routes) (input old : WordTuple 4) :
    r.nextBank input old =
      .cons (counter old - 1) (r.feedback.read (appendTuple old input) PUnit.unit) := by
  obtain ⟨_, _, _, _, rfl⟩ := tuple_pack input
  change Tuple.cons (F := Val model.value) (t := wordPort) (counter old - 1)
      ((extendArguments _ r.feedback).read _ (r.graph.header.eval model _ PUnit.unit)) = _
  rw [extend_read]

private theorem test_zero (old : WordTuple 4) : testWord old = 0 ↔ counter old = 0 := by
  by_cases h : counter old = 0 <;> simp [testWord, ofBool, h]

theorem step_feedback (r : Routes) (input old : WordTuple 4) (fr : Frame Reg)
    (stk : List (Activation Reg)) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input))
    (next : fr.get (.node 1) = some (counter old - 1)) (test : fr.get (.node 3) = some (testWord old))
    (taken : counter old ≠ 0) :
    step r.lower ⟨⟨0, 1, 4⟩, fr, stk, mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindBank fr (r.nextBank input old), stk, mem⟩ := by
  change (match fr.get (.node 3) with
    | none => Result.stuck (R := Reg)
    | some guard => transfer r.lower _ (if guard = 0 then 2 else 1)
      (if guard = 0 then [.arg 5] else r.incomingRegisters .backedge)) = _
  rw [test]
  simp only [ite_eq_right (mt (test_zero old).mp taken)]
  have payload := readColumn_eq r.feedback (appendTuple old input) PUnit.unit fr (word_arguments agree)
  have reads : fr.readAll (r.incomingRegisters .backedge) = some (words (r.nextBank input old)) := by
    rw [feedback_registers, nextBank_eq]
    simp only [Frame.readAll, List.mapM_cons, next]
    unfold Frame.readAll at payload
    rw [payload]
    rfl
  have target : r.lower.block? 0 1 = some r.header := rfl
  have write : fr.writeAll r.header.params (words (r.nextBank input old)) =
    some (bindBank fr (r.nextBank input old)) := bank_write fr _
  simp [transfer, reads, target, write]

private theorem source_step (r : Routes) (input old : WordTuple 4) :
    r.graph.step model input old =
      if counter old = 0 then .inl (first old) else .inr (r.nextBank input old) := by
  obtain ⟨_, _, _, _, rfl⟩ := tuple_pack input
  change (if (counter old != 0) = true then Sum.inr (α := Word) _ else Sum.inl (first old)) = _
  by_cases h : counter old = 0 <;> (simp [h]; rfl)

theorem lowerChecked_eq_some_iff (entry feedback : List Nat) (target : Prog Reg) :
    lowerChecked entry feedback = some target ↔
      ∃ r, checkRoutes entry feedback = some r ∧ r.lowerFunc.WellFormed ∧ target = r.lower := by
  cases check : checkRoutes entry feedback with
  | none => simp [lowerChecked, check]
  | some route =>
    rw [lowerChecked, check]
    change (if route.lowerFunc.WellFormed then some route.lower else none) = some target ↔ _
    by_cases wf : route.lowerFunc.WellFormed <;> simp [wf, eq_comm]

private theorem bank_matches {fr : Frame Reg} {input : WordTuple 4}
    (agree : ArgsMatch fr input) (values : WordTuple 4) :
    ArgsMatch (bindBank fr values) (appendTuple values input) := by
  obtain ⟨c, a, b, d, rfl⟩ := tuple_pack input
  intro p
  rcases p with _ | p
  · change fr.get (.arg 0) = some c
    exact agree .head
  rcases p with _ | p
  · change fr.get (.arg 1) = some a
    exact agree (.tail .head)
  rcases p with _ | p
  · change fr.get (.arg 2) = some b
    exact agree (.tail (.tail .head))
  rcases p with _ | p
  · change fr.get (.arg 3) = some d
    exact agree (.tail (.tail (.tail .head)))
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  rcases p with _ | p
  · rfl
  · nomatch p

private theorem input_matches {fr : Frame Reg} {input old : WordTuple 4}
    (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch fr input := by
  obtain ⟨c, a, b, d, rfl⟩ := tuple_pack input
  intro p
  rcases p with _ | p
  · exact agree .head
  rcases p with _ | p
  · exact agree (.tail .head)
  rcases p with _ | p
  · exact agree (.tail (.tail .head))
  rcases p with _ | p
  · exact agree (.tail (.tail (.tail .head)))
  · nomatch p

private theorem get_counter {fr : Frame Reg} {input old : WordTuple 4}
    (agree : ArgsMatch fr (appendTuple old input)) : fr.get (.arg 4) = some (counter old) := by
  obtain ⟨_, _, _, _, rfl⟩ := tuple_pack input
  exact agree (argumentPort 8 ⟨4, by decide⟩)

private theorem get_first {fr : Frame Reg} {input old : WordTuple 4}
    (agree : ArgsMatch fr (appendTuple old input)) : fr.get (.arg 5) = some (first old) := by
  obtain ⟨_, _, _, _, rfl⟩ := tuple_pack input
  exact agree (argumentPort 8 ⟨5, by decide⟩)

private theorem header_matches {fr : Frame Reg} {input old : WordTuple 4}
    (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (headerFrame fr old) (appendTuple old input) := by
  intro p
  simpa [headerFrame] using agree p

private def atPoint (label pc : Nat) (fr : Frame Reg) (mem : Memory) : State Reg :=
  ⟨⟨0, label, pc⟩, fr, [], mem⟩

/-- Four actual pure instructions run before the routing terminator. -/
private theorem header_prefix (r : Routes) (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) {finish : State Reg}
    (tail : Steps r.lower (atPoint 1 4 (headerFrame fr old) mem) finish) :
    Steps r.lower (atPoint 1 0 fr mem) finish := by
  let one := fr.set (.node 0) 1
  let decremented := one.set (.node 1) (counter old - 1)
  let withZero := decremented.set (.node 2) 0
  have readCounter : fr.get (.arg 4) = some (counter old) := get_counter agree
  have subExec : (Op.binary .sub (.node 1) (.arg 4) (.node 0)).exec one mem = some (decremented, mem) := by
    have read : one.get (.arg 4) = some (counter old) := by simpa [one] using readCounter
    have literal : one.get (.node 0) = some 1 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have testExec : (Op.binary (.cmp .ne) (.node 3) (.arg 4) (.node 2)).exec withZero mem =
      some (headerFrame fr old, mem) := by
    have read : withZero.get (.arg 4) = some (counter old) := by
      simpa [withZero, decremented, one] using readCounter
    have literal : withZero.get (.node 2) = some 0 := rfl
    simp only [Op.exec, read, literal, Option.bind_some]
    rfl
  have s₀ := Transition.op (p := r.lower) (s := atPoint 1 0 fr mem)
    (o := .const (.node 0) 1) rfl (rfl : _ = some (one, mem))
  have s₁ := Transition.op (p := r.lower) (s := atPoint 1 1 one mem) rfl subExec
  have s₂ := Transition.op (p := r.lower) (s := atPoint 1 2 decremented mem)
    (o := .const (.node 2) 0) rfl (rfl : _ = some (withZero, mem))
  have s₃ := Transition.op (p := r.lower) (s := atPoint 1 3 withZero mem) rfl testExec
  exact .head s₀.step_eq (.head s₁.step_eq (.head s₂.step_eq (.head s₃.step_eq tail)))

private theorem exit_step (r : Routes) (fr : Frame Reg) (mem : Memory) (value : Word)
    (read : fr.get (.arg 5) = some value) (halt : fr.get (.node 3) = some 0) :
    step r.lower (atPoint 1 4 fr mem) = .running (atPoint 2 0 (fr.set .phi value) mem) := by
  change (match fr.get (.node 3) with
    | none => Result.stuck (R := Reg)
    | some guard => transfer r.lower _ (if guard = 0 then 2 else 1)
      (if guard = 0 then [.arg 5] else r.incomingRegisters .backedge)) = _
  rw [halt]
  have target : r.lower.block? 0 2 = some exitBlock := rfl
  simp [transfer, Frame.readAll, target, read, atPoint, exitBlock, Frame.writeAll]

theorem header_agrees (r : Routes) (input old : WordTuple 4) (fr : Frame Reg)
    (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps r.lower ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (match r.graph.step model input old with
      | .inl value => ⟨⟨0, 2, 0⟩, (headerFrame fr old).set .phi value, [], mem⟩
      | .inr next => ⟨⟨0, 1, 0⟩, bindBank (headerFrame fr old) next, [], mem⟩) := by
  rw [source_step]
  let after := headerFrame fr old
  have afterAgrees := header_matches agree
  by_cases halt : counter old = 0
  · simp only [ite_eq_left halt]
    have read : after.get (.arg 5) = some (first old) := get_first afterAgrees
    have guard : after.get (.node 3) = some 0 := (test_zero old).mpr halt ▸ rfl
    exact header_prefix r input old fr mem agree (.head (exit_step r after mem _ read guard) .refl)
  · simp only [ite_eq_right halt]
    exact header_prefix r input old fr mem agree
      (.head (step_feedback r input old after [] mem afterAgrees rfl rfl halt) .refl)

private theorem header_returns (r : Routes) (input : WordTuple 4) (mem : Memory)
    {count : Nat} {old : WordTuple 4} {value : sortValue model.value word}
    (source : r.graph.ReturnsAfter model input count old value) :
    ∀ fr : Frame Reg, ArgsMatch fr (appendTuple old input) →
      Behaves r.lower (atPoint 1 0 fr mem) (.returned [value] mem) := by
  refine Graph.ReturnsAfter.rec (g := r.graph) (m := model) (input := input)
    (motive := fun _ old value _ => ∀ fr, ArgsMatch fr (appendTuple old input) →
      Behaves r.lower (atPoint 1 0 fr mem) (.returned [value] mem)) ?_ ?_ source
  · intro old value taken fr agree
    have activation := header_agrees r input old fr mem agree
    rw [taken] at activation
    exact ⟨atPoint 2 0 ((headerFrame fr old).set .phi value) mem, activation, rfl⟩
  · intro _ old next value taken _ ih fr agree
    have activation := header_agrees r input old fr mem agree
    rw [taken] at activation
    have afterAgrees := header_matches agree
    obtain ⟨finish, suffix, observed⟩ := ih (bindBank (headerFrame fr old) next)
      (bank_matches (input_matches afterAgrees) next)
    exact ⟨finish, activation.trans suffix, observed⟩

private theorem source_total (r : Routes) (input old : WordTuple 4) :
    ∃ value : Word, r.graph.ReturnsAfter model input (counter old).toNat old value := by
  generalize measure : (counter old).toNat = count
  induction count generalizing old with
  | zero =>
    have halt : counter old = 0 := BitVec.eq_of_toNat_eq measure
    exact ⟨first old, .exit ((source_step r input old).trans (ite_eq_left halt))⟩
  | succ count ih =>
    have more : counter old ≠ 0 := by
      intro halt
      rw [halt] at measure
      cases measure
    have positive : (1 : Word) ≤ counter old := by
      rw [BitVec.le_def]
      change 1 ≤ (counter old).toNat
      omega
    have dec : (counter (r.nextBank input old)).toNat = count := by
      have eq : counter (r.nextBank input old) = counter old - 1 := by rw [nextBank_eq]; rfl
      rw [eq, BitVec.toNat_sub_of_le positive]
      change (counter old).toNat - 1 = count
      omega
    obtain ⟨value, rest⟩ := ih (r.nextBank input old) dec
    exact ⟨value, .backedge ((source_step r input old).trans (ite_eq_right more)) rest⟩

private theorem source_to_oracle (r : Routes) (input : WordTuple 4) (mem : Memory) (value : Word)
    (source : r.graph.Returns model input value) : r.lower.oracle 0 (words input) mem [value] mem := by
  obtain ⟨c, a, b, d, rfl⟩ := tuple_pack input
  let fr : Frame Reg := (((Frame.empty.set (.arg 0) c).set (.arg 1) a).set (.arg 2) b).set (.arg 3) d
  have agree : ArgsMatch fr (pack c a b d) := by
    intro p
    rcases p with _ | p
    · rfl
    rcases p with _ | p
    · rfl
    rcases p with _ | p
    · rfl
    rcases p with _ | p
    · rfl
    · nomatch p
  let initial := r.graph.initial model (pack c a b d)
  obtain ⟨_, run⟩ := source
  obtain ⟨finish, suffix, observed⟩ := header_returns r (pack c a b d) mem run
    (bindBank fr initial) (bank_matches agree initial)
  exact ⟨atPoint 0 0 fr mem, rfl, finish, .head (step_entry r _ fr [] mem agree) suffix, observed⟩

theorem lower_returns_iff (r : Routes) (input : WordTuple 4) (initial final : Memory) (returned : List Word) :
    r.lower.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, r.graph.Returns model input value ∧ returned = [value] ∧ final = initial := by
  constructor
  · intro actual
    obtain ⟨value, run⟩ := source_total r input (r.graph.initial model input)
    have source : r.graph.Returns model input value := ⟨_, run⟩
    have expected := source_to_oracle r input initial value source
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic r.lower 0 (words input) initial _ _ _ _ actual expected
    exact ⟨value, source, valuesEq, memEq⟩
  · rintro ⟨value, source, rfl, memEq⟩
    subst final
    exact source_to_oracle r input initial value source

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Proofs
