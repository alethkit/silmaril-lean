module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Column
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Correctness
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model word emitOpWith)
open Silmaril.SSA.RVSDG (Origin Port)
open Silmaril.SSA.SeaOfNodes.Diamond (read)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom inputEnv instruction encodeTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} (p : Plan arity)

private theorem index_lt {ports : List PortTy} {t : PortTy} (port : Port ports t) :
    port.index < ports.length := by
  induction port with
  | head => simp [Port.index]
  | tail _ ih => simpa [Port.index] using Nat.succ_lt_succ ih

private theorem initializer_exec (input : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr input) :
    (emitOpWith (fun port => .arg port.index) (initRegister arity)
      p.initializer.operation.source p.initializer.operands).exec fr mem =
        some (fr.set (initRegister arity) (p.initializer.value input), mem) := by
  obtain ⟨operation, operands⟩ := p.initializer
  cases operands with
  | cons left rest =>
    cases rest with
    | cons right tail =>
      cases tail
      cases left with
      | output index _ => exact index.elim0
      | arg lhs =>
        cases right with
        | output index _ => exact index.elim0
        | arg rhs =>
          cases operation <;>
            simp only [Initializer.value, FeedbackOp.source, emitOpWith, Op.exec,
              SSA.RVSDG.Tuple.get, Diamond.RTL.registerWith] <;>
            rw [agree lhs, agree rhs] <;> rfl

theorem entry_packet (input : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr input) :
    let ready := fr.set (initRegister arity) (p.initializer.value input)
    let bank := p.graph.initial model input
    let latched := bindWords arity ready bank
    StepsNWithin p.rtl [] 2 ⟨⟨0, 0, 0⟩, fr, [], mem⟩ ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple bank input) ∧
      Eval (instruction model) (inputEnv model input) (Generic.entry p.graph) mem 0 (encodeTuple model bank) mem := by
  let ready := fr.set (initRegister arity) (p.initializer.value input)
  let bank := p.graph.initial model input
  have captures : ArgsMatch ready input := by
    intro port
    have bound : port.index < arity := by simpa [wordPorts, wordSorts] using index_lt port
    simpa [ready, initRegister, show port.index ≠ arity + arity by omega] using agree port
  have reads : ready.readAll (p.entry.addresses.map (entryRegister arity)) = some (words bank) := by
    apply Routing.Proofs.readColumnWith_eq
    intro wire
    cases wire with
    | arg port => exact captures port
    | output index field =>
      change Fin 1 at index
      have single : index = 0 := Fin.fin_one_eq_zero index
      subst index
      cases field with
      | head =>
        change ready.get (initRegister arity) = some (p.initializer.value input)
        simp [ready]
      | tail impossible => nomatch impossible
  have entryBlock : p.rtl.block? 0 0 = some p.preheader := rfl
  have fetched := Prog.fetch_op entryBlock
    (show p.preheader.ops[0]? = some (emitOpWith (fun port => .arg port.index) (initRegister arity)
      p.initializer.operation.source p.initializer.operands) by rfl)
  have execute := Transition.op (s := (⟨⟨0, 0, 0⟩, fr, [], mem⟩ : State Reg))
    fetched (initializer_exec p input fr mem agree)
  have jump : step p.rtl ⟨⟨0, 0, 1⟩, ready, [], mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindWords arity ready bank, [], mem⟩ := by
    have fetchJump : p.rtl.fetch ⟨0, 0, 1⟩ = some (.term p.preheader.term) := Prog.fetch_term entryBlock
    simp only [step, fetchJump, Plan.preheader]
    exact Routing.Proofs.transfer_bank_from p.row.graph p.preheader _ _ _ rfl reads
  exact ⟨.head ⟨execute.step_eq, List.nil_suffix⟩ (.head ⟨jump, List.nil_suffix⟩ .refl),
    bank_matches_at captures bank, Generic.entry_eval p.graph model input mem⟩

theorem header_packet (input old : WordTuple arity) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple old input)) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (Generic.header p.graph) mem
    let after := p.row.testFrame fr old
    match p.graph.step model input old with
    | .inl value =>
      StepsNWithin p.rtl [] p.row.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 2, 0⟩, after.set .phi value, [], mem⟩ ∧
      eval 1 (Generic.packResult model (out := word) value) mem
    | .inr next =>
      let latched := bindWords arity after next
      StepsNWithin p.rtl [] p.row.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple next input) ∧ eval 0 (encodeTuple model next) mem := by
  have rtl := Rows.Proofs.header_activation_steps_from p.row p.preheader input old fr mem agree
  have typed := Generic.header_eval p.graph model input old mem
  have branch : p.graph.step model input old =
      if p.row.guardWord old = 0 then .inl (p.row.exitValue old) else .inr (p.row.nextBank input old) :=
    Rows.native_step p.row input old fr agree
  dsimp only
  rw [branch] at typed ⊢
  by_cases exit : p.row.guardWord old = 0
  · rw [ite_eq_left exit] at typed ⊢
    exact ⟨by simpa only [Plan.rtl, Rows.Plan.successor, ite_eq_left exit] using rtl, typed⟩
  · rw [ite_eq_right exit] at typed ⊢
    exact ⟨by simpa only [Plan.rtl, Rows.Plan.successor, ite_eq_right exit] using rtl,
      bank_matches_at (input_matches_at (Rows.testFrame_args p.row input old fr agree)) _, typed⟩

private theorem returnsAfter_congr {leftEntry rightEntry sigs : List (List PortTy)}
    (left : Graph Diamond.RTL.WordOp (wordSorts arity) (wordSorts arity) leftEntry sigs word)
    (right : Graph Diamond.RTL.WordOp (wordSorts arity) (wordSorts arity) rightEntry sigs word)
    (input : WordTuple arity) (same : ∀ old, left.step model input old = right.step model input old)
    {count : Nat} {old : WordTuple arity} {value : Word}
    (source : left.ReturnsAfter model input count old value) : right.ReturnsAfter model input count old value := by
  refine Graph.ReturnsAfter.rec (g := left) (m := model) (input := input)
    (motive := fun count old value _ => right.ReturnsAfter model input count old value) ?_ ?_ source
  · intro old value taken
    exact .exit ((same old).symm.trans taken)
  · intro count old next value taken _ ih
    exact .backedge ((same old).symm.trans taken) ih

private theorem returnsAfter_row (input old : WordTuple arity) (count : Nat) (value : Word) :
    p.graph.ReturnsAfter model input count old value ↔ p.row.graph.ReturnsAfter model input count old value :=
  ⟨returnsAfter_congr p.graph p.row.graph input (fun _ => rfl),
    returnsAfter_congr p.row.graph p.graph input (fun _ => rfl)⟩

theorem runMain_fuel_iff (input : WordTuple arity) (initial final : Memory)
    (returned : List Word) (fuel : Nat) :
    p.rtl.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.graph.ReturnsAfter model input count (p.graph.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  let fr := bindWords 0 Frame.empty input
  let atEntry : State Reg := ⟨⟨0, 0, 0⟩, fr, [], initial⟩
  have start : p.rtl.start 0 (words input) initial = some atEntry := by
    change ((Frame.empty.writeAll (paramRegs 0 arity) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
      (fun entered => (⟨entered.1, entered.2, [], initial⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  obtain ⟨prefixPath, agree, _⟩ := entry_packet p input fr initial (bindWords_args input)
  let old := p.graph.initial model input
  let next := bindWords arity (fr.set (initRegister arity) (p.initializer.value input)) old
  have loop := Rows.Proofs.header_run_fuel_iff p.row p.preheader input old next agree initial final returned
  simp only [Prog.runMain, start]
  constructor
  · intro observed
    obtain ⟨remaining, spent, rest⟩ := run_after_prefix prefixPath observed
    obtain ⟨count, value, source, bound, outputs, memory⟩ := (loop remaining).mp rest
    exact ⟨count, value, (returnsAfter_row p input old count value).mpr source,
      by unfold Plan.rtlFuel Rows.Plan.rtlFuel; omega, outputs, memory⟩
  · rintro ⟨count, value, source, enough, outputs, memory⟩
    have bound : p.row.activationSteps * (count + 1) + 1 ≤ fuel - 2 := by
      unfold Plan.rtlFuel Rows.Plan.rtlFuel at enough
      omega
    have spent : fuel = 2 + (fuel - 2) := by omega
    rw [spent, run_through_prefix prefixPath]
    exact (loop (fuel - 2)).mpr
      ⟨count, value, (returnsAfter_row p input old count value).mp source, bound, outputs, memory⟩

private theorem rtl_returns (input : WordTuple arity) (initial final : Memory) (returned : List Word) :
    p.rtl.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, p.graph.Returns model input value ∧ returned = [value] ∧ final = initial := by
  constructor
  · rintro ⟨start, started, finish, steps, result⟩
    obtain ⟨fuel, run⟩ := fuel_of_steps steps result
    have whole : p.rtl.runMain fuel 0 (words input) initial = .returned returned final := by
      simpa only [Prog.runMain, started] using run
    obtain ⟨count, value, source, _, same, memory⟩ :=
      (runMain_fuel_iff p input initial final returned fuel).mp whole
    exact ⟨value, ⟨count, source⟩, same, memory⟩
  · rintro ⟨value, ⟨count, source⟩, rfl, memory⟩
    subst final
    have whole := (runMain_fuel_iff p input initial initial [value] (p.rtlFuel count)).mpr
      ⟨count, value, source, le_rfl, rfl, rfl⟩
    unfold Prog.runMain at whole
    split at whole
    · exact ⟨_, by assumption, run_returned whole⟩
    · cases whole

section Checked

variable {sigs : List (List PortTy)} {g : Source arity sigs} {targets : Checked.Phi.Targets}

theorem lowerChecked_sound (accepted : lowerChecked g = some targets) :
    ∃ p, recognize g = some p ∧ p.lowerFunc.WellFormed ∧
      targets = (p.rtl, Generic.lower g) := by
  unfold lowerChecked at accepted
  cases found : recognize g with
  | none => simp [found] at accepted
  | some p =>
    simp only [found, Option.bind_some] at accepted
    split at accepted
    · exact ⟨p, rfl, by assumption, (Option.some.inj accepted).symm⟩
    · cases accepted

theorem lowerChecked_typed (accepted : lowerChecked g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts arity))
      [Generic.packed [.value word]] := by
  obtain ⟨p, _, wellFormed, rfl⟩ := lowerChecked_sound accepted
  exact ⟨by simpa [Plan.rtl, Plan.lowerFunc, lowerBankFrom, Prog.WellFormed] using wellFormed, Generic.lower_hasType g⟩

theorem rtl_runMain_fuel_iff {p : Plan arity} (recognized : recognize g = some p)
    (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) (fuel : Nat) :
    targets.1.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, g.ReturnsAfter model input count (g.initial model input) value ∧
        p.rtlFuel count ≤ fuel ∧ returned = [value] ∧ final = initial := by
  obtain ⟨q, found, _, rfl⟩ := lowerChecked_sound accepted
  cases Option.some.inj (found.symm.trans recognized)
  obtain ⟨rfl, rfl⟩ := recognize_sound found
  exact runMain_fuel_iff p input initial final returned fuel

theorem lambda_run_succ (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (budget : Nat) :
    Generic.Fuel.run model (inputEnv model input) (budget + 1) targets.2 =
      (g.evalBackedges model budget input).map (fun value => (0, Generic.packResult model (out := word) value)) := by
  obtain ⟨_, _, _, rfl⟩ := lowerChecked_sound accepted
  exact Generic.Fuel.run_succ g model input budget

theorem rtl_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, g.Returns model input value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨p, recognized, _, rfl⟩ := lowerChecked_sound accepted
  obtain ⟨rfl, rfl⟩ := recognize_sound recognized
  exact rtl_returns p input initial final returned

theorem lambda_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, g.Returns model input value ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial := by
  obtain ⟨_, _, _, rfl⟩ := lowerChecked_sound accepted
  exact Generic.lower_eval_iff g model input initial final label payload

theorem no_finite_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        g.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ g.denote model input = Part.none) := by
  have native : g.denote model input = Part.none ↔ ∀ value, ¬ g.Returns model input value := by
    simp only [Part.eq_none_iff', Part.dom_iff_mem, not_exists, g.returns_iff_mem_denote]
  constructor
  · rw [native]
    constructor
    · intro absent value source
      exact absent [value] initial ((rtl_return_iff accepted input initial initial [value]).mpr
        ⟨value, source, rfl, rfl⟩)
    · intro absent returned final run
      obtain ⟨value, source, _, _⟩ := (rtl_return_iff accepted input initial final returned).mp run
      exact absent value source
  · rw [native]
    constructor
    · intro absent value source
      exact absent 0 (Generic.packResult model (out := word) value) initial
        ((lambda_return_iff accepted input initial initial 0 _).mpr ⟨value, source, rfl, rfl, rfl⟩)
    · intro absent label payload final run
      obtain ⟨value, source, _, _, _⟩ := (lambda_return_iff accepted input initial final label payload).mp run
      exact absent value source

end Checked

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Proofs
