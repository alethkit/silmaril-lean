module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Thms
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Proofs

open RVSDG (Port Tuple)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (i1)
open Silmaril.MLIR.SCF.For (weakenVar)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)
open Memory.Diamond.MLIR.Finite hiding entryTypes encodeEntry entryHeap lower Label

variable {args : List ValueSort}
variable (p : Profile) (graph : Graph args) (input : Tuple (Val p.cells) args)
variable (initial : Heap p.cells)

private def headerFrame (p : Profile) (heap : Heap p.cells) : Frame (Label p) :=
  ⟨.header, encodeHeap heap⟩

private def testFrame (p : Profile) (word : Word) (heap : Heap p.cells) : Frame (Label p) :=
  ⟨.test, encodeResult p word heap⟩

private def exitFrame (p : Profile) (word : Word) (heap : Heap p.cells) : Frame (Label p) :=
  ⟨.exit, encodeResult p word heap⟩

private theorem entryVar_get {sort : ValueSort} (port : Port args sort) :
    (encodeEntry p input initial).get (entryVar p port) = encodeValue p (input.get port) :=
  (get_weakenVar (encodeHeap initial) (encodeScalars p input) (argVar port)).trans
    (get_encodeScalars_argVar input port)

private theorem entry_eval :
    (lower p graph).entry.eval evalOp (fun term env => term.eval env) (encodeEntry p input initial) =
      .inl (headerFrame p initial) := by
  apply congrArg (fun cells => Sum.inl (Frame.mk (Label.header (p := p)) cells))
  apply eval_heapOperands
  intro index
  exact (get_appendVar (cellVar index) (encodeHeap initial) (encodeScalars p input)).trans
    (get_encodeHeap_cellVar initial index)

private theorem header_eval (heap : Heap p.cells) :
    (headerBlock p graph).eval evalOp (fun term env => term.eval env)
      ((encodeHeap heap).append (encodeEntry p input initial)) =
      let result := graph.body.denote input heap
      Sum.inl (testFrame p result.1 result.2) := by
  refine eval_lowerBody (Term := Terminator (Label p) (resultTypes p)) graph.body
    (fun word heap => .br ⟨.test, resultOperands word heap⟩) (fun term env => term.eval env)
    (fun word final => Sum.inl (testFrame p word final)) ?_
    (headerRoute p args) (headerHeap p args) _ input PUnit.unit heap ?_ ?_
  · intro Δ word refs env final ok
    exact congrArg (fun values => Sum.inl (Frame.mk (Label.test (p := p)) values))
      (eval_resultOperands word refs env final ok)
  · intro sort wire
    cases wire with
    | arg port =>
      exact (get_weakenVar (encodeHeap heap) (encodeEntry p input initial) (entryVar p port)).trans
        (entryVar_get p input initial port)
    | output index _ => exact index.elim0
  · intro index
    exact (get_appendVar (cellVar index) (encodeHeap heap) (encodeEntry p input initial)).trans
      (get_encodeHeap_cellVar heap index)

private theorem resultHeap_agrees (word : Word) (heap : Heap p.cells) :
    HeapAgrees (p := p) (resultHeap p args) ((encodeResult p word heap).append (encodeEntry p input initial))
      heap :=
  fun index =>
    (get_appendVar (.there (cellVar index)) (encodeResult p word heap) (encodeEntry p input initial)).trans
      (get_encodeHeap_cellVar heap index)

private theorem test_eval (word : Word) (heap : Heap p.cells) :
    (testBlock p graph).eval evalOp (fun term env => term.eval env)
      ((encodeResult p word heap).append (encodeEntry p input initial)) =
      .inl (if word = graph.stopWord input then exitFrame p word heap else headerFrame p heap) := by
  let env := (encodeResult p word heap).append (encodeEntry p input initial)
  let stop := weakenVar (entryVar p graph.stop) (resultTypes p)
  let bit := BitVec.ofBool (decide (word = env.get stop))
  let tested := Env.cons (w := i1) bit env
  let refs : HeapRefs p.cells (i1 :: (resultTypes p ++ entryTypes p args)) :=
    fun index => .there (resultHeap p args index)
  change Sum.inl (if bit.getLsbD 0 then
      Frame.mk (Label.exit (p := p)) ((resultOperands (.there .here) refs).eval tested)
    else Frame.mk (Label.header (p := p)) ((heapOperands refs).eval tested)) = _
  have stop_ok : env.get stop = graph.stopWord input :=
    (get_weakenVar (encodeResult p word heap) (encodeEntry p input initial) (entryVar p graph.stop)).trans
      (entryVar_get p input initial graph.stop)
  have cells_ok : HeapAgrees refs tested heap := resultHeap_agrees p input initial word heap
  rw [eval_resultOperands _ _ _ _ cells_ok, eval_heapOperands _ _ _ cells_ok]
  change Sum.inl (if (BitVec.ofBool (decide (word = env.get stop))).getLsbD 0 then
    exitFrame p word heap else headerFrame p heap) = _
  rw [stop_ok, BitVec.getLsbD_ofBool]
  by_cases equal : word = graph.stopWord input <;> simp [equal]

private theorem exit_eval (word : Word) (heap : Heap p.cells) :
    ((lower p graph).block .exit).eval evalOp (fun term env => term.eval env)
      ((encodeResult p word heap).append (encodeEntry p input initial)) =
      .inr (encodeResult p word heap) := by
  exact congrArg Sum.inr (eval_resultOperands .here _ _ _ (resultHeap_agrees p input initial word heap))

private theorem run_entry (fuel : Nat) :
    (lower p graph).run evalOp (fuel + 1) (encodeEntry p input initial) =
      (lower p graph).runFrom evalOp fuel (encodeEntry p input initial) (headerFrame p initial) := by
  unfold Cfg.run
  rw [Cfg.runBlock, entry_eval]
  rfl

private theorem run_exit (fuel : Nat) (word : Word) (heap : Heap p.cells) :
    (lower p graph).runFrom evalOp fuel (encodeEntry p input initial) (exitFrame p word heap) =
      if fuel = 0 then none else some (encodeResult p word heap) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    change (lower p graph).runBlock evalOp (encodeEntry p input initial) (fuel + 1)
      ((lower p graph).block .exit) ((encodeResult p word heap).append (encodeEntry p input initial)) = _
    rw [Cfg.runBlock, exit_eval]
    rfl

private theorem run_header (fuel : Nat) (heap : Heap p.cells) :
    (lower p graph).runFrom evalOp (fuel + 2) (encodeEntry p input initial) (headerFrame p heap) =
      match graph.step input heap with
      | .inl (word, final) => if fuel = 0 then none else some (encodeResult p word final)
      | .inr next => (lower p graph).runFrom evalOp fuel (encodeEntry p input initial) (headerFrame p next) := by
  change (lower p graph).runBlock evalOp (encodeEntry p input initial) (fuel + 1 + 1)
    (headerBlock p graph) ((encodeHeap heap).append (encodeEntry p input initial)) = _
  rw [Cfg.runBlock, header_eval]
  unfold Graph.step
  rcases evaluated : graph.body.denote input heap with ⟨word, final⟩
  change (lower p graph).runBlock evalOp (encodeEntry p input initial) (fuel + 1)
    (testBlock p graph) ((encodeResult p word final).append (encodeEntry p input initial)) = _
  rw [Cfg.runBlock, test_eval]
  change (lower p graph).runFrom evalOp fuel (encodeEntry p input initial)
      (if word = graph.stopWord input then exitFrame p word final else headerFrame p final) =
    match (if word = graph.stopWord input then Sum.inl (word, final) else Sum.inr final) with
    | .inl (word, final) => if fuel = 0 then none else some (encodeResult p word final)
    | .inr next => (lower p graph).runFrom evalOp fuel (encodeEntry p input initial) (headerFrame p next)
  by_cases equal : word = graph.stopWord input
  · simp only [ite_eq_left equal]
    exact run_exit p graph input initial fuel word final
  · simp only [ite_eq_right equal]

private theorem header_run_eq_some (fuel : Nat) (heap : Heap p.cells) (output : Env (resultTypes p)) :
    (lower p graph).runFrom evalOp fuel (encodeEntry p input initial) (headerFrame p heap) = some output ↔
      ∃ count word final, 2 * count + 3 ≤ fuel ∧ graph.evalFrom input count heap = some (word, final) ∧
        output = encodeResult p word final := by
  induction fuel using Nat.strong_induction_on generalizing heap with
  | ind fuel ih =>
    match fuel with
    | 0 => simp [Cfg.runFrom, Cfg.runBlock]
    | 1 =>
      change (lower p graph).runBlock evalOp (encodeEntry p input initial) 1
        (headerBlock p graph) ((encodeHeap heap).append (encodeEntry p input initial)) = some output ↔ _
      rw [Cfg.runBlock, header_eval]
      simp [Cfg.runBlock, show ∀ count : Nat, ¬ 2 * count + 3 ≤ 1 by omega]
    | fuel + 2 =>
      rw [run_header]
      cases step : graph.step input heap with
      | inl result =>
        rcases result with ⟨word, final⟩
        change (if fuel = 0 then none else some (encodeResult p word final)) = some output ↔ _
        constructor
        · intro observed
          have enough : fuel ≠ 0 := by
            intro empty
            simp [empty] at observed
          rw [ite_eq_right enough] at observed
          exact ⟨0, word, final, by omega, by simp [Graph.evalFrom, step], (Option.some.inj observed).symm⟩
        · rintro ⟨count, value, heap', enough, observed, rfl⟩
          cases count with
          | zero =>
            simp only [Graph.evalFrom, step, Option.some.injEq, Prod.mk.injEq] at observed
            obtain ⟨rfl, rfl⟩ := observed
            rw [ite_eq_right (by omega : fuel ≠ 0)]
          | succ count => simp [Graph.evalFrom, step] at observed
      | inr next =>
        rw [ih fuel (by omega) next]
        constructor
        · rintro ⟨count, word, final, enough, observed, rfl⟩
          exact ⟨count + 1, word, final, by omega, by simpa [Graph.evalFrom, step] using observed, rfl⟩
        · rintro ⟨count, word, final, enough, observed, rfl⟩
          cases count with
          | zero => simp [Graph.evalFrom, step] at observed
          | succ count => exact ⟨count, word, final, by omega, by simpa [Graph.evalFrom, step] using observed, rfl⟩

theorem lower_run_eq_some (fuel : Nat) (output : Env (resultTypes p)) :
    (lower p graph).run evalOp fuel (encodeEntry p input initial) = some output ↔
      ∃ count word final, 2 * count + 4 ≤ fuel ∧ graph.ReturnsAfter input initial count word final ∧
        output = encodeResult p word final := by
  cases fuel with
  | zero => simp [Cfg.run, Cfg.runBlock]
  | succ fuel =>
    rw [run_entry, header_run_eq_some]
    simp only [Graph.returnsAfter_iff_evalAfter, Graph.evalAfter, Nat.add_succ, Nat.succ_le_succ_iff]

theorem lower_returns_iff (word : Word) (final : Heap p.cells) :
    graph.Returns input initial word final ↔
      ∃ fuel, (lower p graph).run evalOp fuel (encodeEntry p input initial) = some (encodeResult p word final) := by
  constructor
  · rintro ⟨count, returned⟩
    exact ⟨2 * count + 4, (lower_run_eq_some p graph input initial _ _).2
      ⟨count, word, final, le_rfl, returned, rfl⟩⟩
  · rintro ⟨fuel, run⟩
    obtain ⟨count, value, heap, _, returned, same⟩ := (lower_run_eq_some p graph input initial fuel _).1 run
    have eq : (word, final) = (value, heap) := encodeResult_injective p same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    exact ⟨count, returned⟩

theorem lower_denotePart :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower p graph)).denotePart evalOp (encodeEntry p input initial) =
      (graph.denote input initial).map (fun result => Outcome.returned (encodeResult p result.1 result.2)) := by
  apply Part.ext
  intro outcome
  rw [Silmaril.MLIR.CF.SwitchAssert.Cfg.mem_denotePart_iff]
  simp only [Silmaril.MLIR.CF.SwitchAssert.Cfg.embed_run, Option.map_eq_some_iff]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    obtain ⟨count, word, final, _, returned, rfl⟩ := (lower_run_eq_some p graph input initial fuel output).1 run
    exact Part.mem_map _ ((graph.returns_iff_mem_denote input initial word final).1 ⟨count, returned⟩)
  · intro observed
    obtain ⟨⟨word, final⟩, native, rfl⟩ := (Part.mem_map_iff _).1 observed
    obtain ⟨fuel, run⟩ := (lower_returns_iff p graph input initial word final).1
      ((graph.returns_iff_mem_denote input initial word final).2 native)
    exact ⟨fuel, _, run, rfl⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Proofs
