module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Theta.Activation
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.ThetaProofs

open RVSDG (Locals Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Threaded runtimePort)

set_option backward.isDefEq.respectTransparency false

variable {args : List ValueSort} {cells : Nat}

/-- Count mandatory body activations, as the numbered target's fuel does. -/
private def within (graph : Graph args) (input : Tuple (Val cells) args) : Nat → Heap cells → Option (Heap cells)
  | 0, _ => none
  | fuel + 1, heap => match graph.step input heap with
    | .inl result => some result.2
    | .inr next => within graph input fuel next

private def activation (graph : Graph args) (fuel : Nat) (entry : Tuple (WireVal cells) (carrier args)) :
    Option (Tuple (WireVal cells) (RVSDG.Theta.BodyResults (carrier args))) :=
  (RVSDG.NestedTheta.Term.ofBase graph.thetaBody).run (thetaRuntime cells) fuel entry

private theorem iterate_eq (graph : Graph args) (input : Tuple (Val cells) args)
    (ambient fuel : Nat) (heap : Heap cells) :
    RVSDG.NestedTheta.iterate (activation graph ambient)
      (fun tag => tag.down.val == 1) fuel (encodeInput heap input) =
      (within graph input fuel heap).map (fun h => encodeInput h input) := by
  induction fuel generalizing heap with
  | zero => rfl
  | succ fuel ih =>
    let out := graph.body.denote input heap
    have body : activation graph ambient (encodeInput heap input) =
        some (.cons (continueTag out.1 (graph.stopWord input)) (encodeInput out.2 input)) :=
      (RVSDG.NestedTheta.Term.run_ofBase graph.thetaBody (thetaRuntime cells) ambient
        (encodeInput heap input)).trans (congrArg some (body_run graph input heap))
    refine (RVSDG.NestedTheta.iterate.eq_2 (activation graph ambient) (fun tag => tag.down.val == 1)
      (encodeInput heap input) fuel).trans ?_
    rw [body]
    by_cases stop : (graph.body.denote input heap).1 = graph.stopWord input
    · simp [out, within, Graph.step, continueTag, stop]
    · simpa [out, within, Graph.step, continueTag, stop] using ih (graph.body.denote input heap).2

private theorem get_heap (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (runtimePort (dataPorts args)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (fuel : Nat) :
    graph.lowerTheta.run (thetaRuntime cells) fuel (encodeInput initial input) =
      (within graph input fuel initial).map (encodeResult (graph.stopWord input)) := by
  rw [Graph.lowerTheta, ← RVSDG.NestedTheta.Graph.run_toTerm, RVSDG.NestedTheta.Term.toTerm_toGraph]
  let entry := encodeInput initial input
  let exit := fun (result : Tuple (WireVal cells) (carrier args)) =>
    encodeResult (result.get (argumentPort graph.stop)) (result.get (runtimePort (dataPorts args)))
  change (RVSDG.NestedTheta.iterate (activation graph fuel) (fun tag => tag.down.val == 1) fuel
      (Wires.read (SeaOfNodes.Loop.argWires (carrier args) []) entry PUnit.unit)).bind
      (fun output => some (exit output)) = _
  rw [read_args]
  refine (congrArg (fun r => r.bind (fun output => some (exit output)))
    (iterate_eq graph input fuel fuel initial)).trans ?_
  cases within graph input fuel initial with
  | none => rfl
  | some heap =>
    change some (exit (encodeInput heap input)) = _
    simp only [exit, encodeInput_get, get_heap, Option.map_some, Graph.stopWord]

private theorem stop_eq {graph : Graph args} {input : Tuple (Val cells) args} {heap : Heap cells}
    {result : Word × Heap cells} (stop : graph.step input heap = .inl result) :
    result.1 = graph.stopWord input := by
  change (if (graph.body.denote input heap).1 = graph.stopWord input then Sum.inl (graph.body.denote input heap)
    else Sum.inr (graph.body.denote input heap).2) = Sum.inl result at stop
  split at stop
  next test => exact (congrArg Prod.fst (Sum.inl.inj stop)).symm.trans test
  next => cases stop

private theorem exact_count (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (count : Nat) (value : Word) (final : Heap cells) :
    graph.evalFrom input count heap = some (value, final) ↔
      value = graph.stopWord input ∧ within graph input count heap = none ∧
        within graph input (count + 1) heap = some final := by
  induction count generalizing heap with
  | zero =>
    cases step : graph.step input heap with
    | inl result =>
      have test := stop_eq step
      simp only [Graph.evalFrom, within, step, Option.some.injEq, true_and]
      constructor
      · intro eq
        cases eq
        exact ⟨test, rfl⟩
      · rintro ⟨word, heap⟩
        exact Prod.ext (test.trans word.symm) heap
    | inr next => simp [Graph.evalFrom, within, step]
  | succ count ih =>
    cases step : graph.step input heap with
    | inl result => simp [Graph.evalFrom, within, step]
    | inr next => simpa only [Graph.evalFrom, within, step] using ih next

private theorem within_sound (graph : Graph args) (input : Tuple (Val cells) args)
    (fuel : Nat) (heap final : Heap cells) (run : within graph input fuel heap = some final) :
    ∃ count, graph.evalFrom input count heap = some (graph.stopWord input, final) := by
  induction fuel generalizing heap with
  | zero => simp [within] at run
  | succ fuel ih =>
    cases step : graph.step input heap with
    | inl result =>
      have state := Option.some.inj (by simpa only [within, step] using run : some result.2 = some final)
      have out : result = (graph.stopWord input, final) := Prod.ext (stop_eq step) state
      exact ⟨0, by simp only [Graph.evalFrom, step, out]⟩
    | inr next =>
      obtain ⟨count, rest⟩ := ih next (by simpa only [within, step] using run)
      exact ⟨count + 1, by simpa only [Graph.evalFrom, step] using rest⟩

private theorem map_encode_none (word : Word) (state : Option (Heap cells)) :
    state.map (encodeResult word) = none ↔ state = none := by
  cases state <;> simp

private theorem map_encode_some (word value : Word) (state : Option (Heap cells)) (final : Heap cells) :
    state.map (encodeResult word) = some (encodeResult value final) ↔
      value = word ∧ state = some final := by
  cases state with
  | none => simp
  | some heap =>
    simp only [Option.map_some, Option.some.injEq]
    constructor
    · intro eq
      exact ⟨(congrArg (fun (xs : Tuple (WireVal cells) (Threaded wordPorts)) => xs.get .head) eq).symm,
        congrArg (fun (xs : Tuple (WireVal cells) (Threaded wordPorts)) => xs.get (.tail .head)) eq⟩
    · rintro ⟨rfl, rfl⟩
      rfl

theorem lower_returnsAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (value : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial count value final ↔
      graph.lowerTheta.run (thetaRuntime cells) count (encodeInput initial input) = none ∧
      graph.lowerTheta.run (thetaRuntime cells) (count + 1) (encodeInput initial input) =
        some (encodeResult value final) := by
  rw [graph.returnsAfter_iff_evalAfter, Graph.evalAfter, exact_count, lower_run, lower_run,
    map_encode_none, map_encode_some]
  exact ⟨fun ⟨word, small, complete⟩ => ⟨small, word, complete⟩,
    fun ⟨small, word, complete⟩ => ⟨word, small, complete⟩⟩

theorem lower_returns (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔
      graph.lowerTheta.Returns (thetaRuntime cells) (encodeInput initial input) (encodeResult value final) := by
  constructor
  · rintro ⟨count, run⟩
    exact ⟨count + 1, ((lower_returnsAfter graph input initial count value final).mp run).2⟩
  · rintro ⟨fuel, run⟩
    rw [lower_run, map_encode_some] at run
    obtain ⟨rfl, finished⟩ := run
    obtain ⟨count, evaluated⟩ := within_sound graph input fuel initial final finished
    exact ⟨count, (graph.returnsAfter_iff_evalAfter input initial count _ final).mpr evaluated⟩

theorem lower_run_none (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (fixed : graph.step input heap = .inr heap) (fuel : Nat) :
    graph.lowerTheta.run (thetaRuntime cells) fuel (encodeInput heap input) = none := by
  rw [lower_run, map_encode_none]
  induction fuel with
  | zero => rfl
  | succ _ ih => simpa only [within, fixed] using ih

end Silmaril.SSA.SeaOfNodes.Memory.Loop.ThetaProofs
