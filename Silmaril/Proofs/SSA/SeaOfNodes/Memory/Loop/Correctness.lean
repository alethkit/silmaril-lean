module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Semantics.Elgot.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Proofs

open RVSDG (Tuple)
open SeaOfNodes.Loop (Incoming)
open Silmaril.Elgot.Part (Runs mem_run_iff)

variable {args : List ValueSort} {cells : Nat}
variable {graph : Graph args} {input : Tuple (Val cells) args}
variable {initial heap final : Heap cells} {value : Word}
variable {edge : Incoming} {operand : Operand cells edge} {count : Nat}

private theorem step_exit :
    graph.step input heap = .inl (value, final) ↔
      graph.body.Returns input heap value final ∧ value = graph.stopWord input := by
  simp only [Memory.Graph.returns_iff_denote, Graph.step]
  split
  next stop =>
    rw [Sum.inl.injEq]
    exact ⟨fun eq => ⟨eq, (congrArg Prod.fst eq).symm.trans stop⟩, And.left⟩
  next continues =>
    constructor
    · intro eq
      cases eq
    · rintro ⟨eq, stop⟩
      exact False.elim (continues ((congrArg Prod.fst eq).trans stop))

private theorem step_backedge :
    graph.step input heap = .inr final ↔
      ∃ word, graph.body.Returns input heap word final ∧ word ≠ graph.stopWord input := by
  simp only [Memory.Graph.returns_iff_denote, Graph.step]
  split
  next stop =>
    constructor
    · intro eq
      cases eq
    · rintro ⟨_, eq, continues⟩
      exact False.elim (continues ((congrArg Prod.fst eq).symm.trans stop))
  next continues =>
    rw [Sum.inr.injEq]
    exact ⟨fun eq => ⟨_, Prod.ext rfl eq, continues⟩,
      fun ⟨_, eq, _⟩ => congrArg Prod.snd eq⟩

private theorem eval_complete (run : graph.ReturnsFrom input initial edge operand count value final) :
    graph.evalFrom input count (latch initial edge operand) = some (value, final) := by
  induction run with
  | exit fired test =>
    have step := step_exit.mpr ⟨fired, test⟩
    rw [Graph.evalFrom, step]
  | backedge fired test _ ih =>
    have step := step_backedge.mpr ⟨_, fired, test⟩
    rw [Graph.evalFrom, step]
    exact ih

private theorem eval_sound
    (evaluated : graph.evalFrom input count (latch initial edge operand) = some (value, final)) :
    graph.ReturnsFrom input initial edge operand count value final := by
  induction count generalizing edge with
  | zero =>
    cases step : graph.step input (latch initial edge operand) with
    | inl result =>
      have eq := Option.some.inj (by simpa only [Graph.evalFrom, step] using evaluated :
        some result = some (value, final))
      obtain ⟨fired, test⟩ := step_exit.mp (step.trans (congrArg Sum.inl eq))
      exact .exit fired test
    | inr next => simp [Graph.evalFrom, step] at evaluated
  | succ count ih =>
    cases step : graph.step input (latch initial edge operand) with
    | inl result => simp [Graph.evalFrom, step] at evaluated
    | inr next =>
      obtain ⟨word, fired, test⟩ := step_backedge.mp step
      have tail : graph.evalFrom input count next = some (value, final) := by
        simpa only [Graph.evalFrom, step] using evaluated
      exact .backedge fired test (ih (edge := .backedge) (operand := next) tail)

theorem returnsAfter_iff_evalAfter (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (count : Nat) (value : Word) (final : Heap cells) :
    graph.ReturnsAfter input initial count value final ↔
      graph.evalAfter input initial count = some (value, final) :=
  ⟨eval_complete, fun run => eval_sound (edge := .entry) (operand := PUnit.unit) run⟩

private theorem returns_to_runs (run : graph.ReturnsFrom input initial edge operand count value final) :
    Runs (fun heap => Part.some (graph.step input heap)) (latch initial edge operand) (value, final) := by
  induction run with
  | exit fired test => exact .done (Part.mem_some_iff.mpr (step_exit.mpr ⟨fired, test⟩).symm)
  | backedge fired test _ ih =>
    exact .more (Part.mem_some_iff.mpr (step_backedge.mpr ⟨_, fired, test⟩).symm) ih

private theorem runs_to_returns {result : Word × Heap cells}
    (run : Runs (fun heap => Part.some (graph.step input heap)) heap result)
    (arrival : latch initial edge operand = heap) :
    ∃ count, graph.ReturnsFrom input initial edge operand count result.1 result.2 := by
  induction run generalizing edge with
  | @done current observed taken =>
    subst current
    obtain ⟨fired, test⟩ := step_exit.mp (Part.mem_some_iff.mp taken).symm
    exact ⟨0, .exit fired test⟩
  | @more current next observed taken _ ih =>
    subst current
    obtain ⟨word, fired, test⟩ := step_backedge.mp (Part.mem_some_iff.mp taken).symm
    obtain ⟨count, rest⟩ := ih (edge := .backedge) (operand := next) rfl
    exact ⟨count + 1, .backedge fired test rest⟩

theorem returns_iff_mem_denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔ (value, final) ∈ graph.denote input initial := by
  rw [Graph.denote, mem_run_iff]
  exact ⟨fun ⟨_, run⟩ => returns_to_runs run, fun run => runs_to_returns run rfl⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Proofs
