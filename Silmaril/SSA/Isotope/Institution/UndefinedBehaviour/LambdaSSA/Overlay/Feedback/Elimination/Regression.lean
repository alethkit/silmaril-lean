module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Thms

/-! Both kinds of infinite replay and the priority of reachable inner UB. -/

open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

namespace LambdaSSAFeedbackEliminationRegression

private inductive Node where
  | start
  | outer
  | inner

private def inside (p : Node) : Prop := p = .inner

private def tailGraph : Graph Node Bool where
  step p q := match p with
    | .start => q = .outer
    | .outer | .inner => q = .inner
  ub _ := False
  finish _ _ := False
  divergence := false

private theorem tail_segment {p q : Node} (h : (tailGraph.outer inside).step p q) :
    p = .start ∧ q = .outer := by
  obtain ⟨_, b, pending, edge, outside⟩ := Graph.outer_step_iff.mp h
  cases b with
  | start =>
    have source : p = .start := by
      cases pending with
      | refl => rfl
      | tail _ edge => exact False.elim (by simpa [Graph.inner, inside] using edge.2)
    exact ⟨source, edge⟩
  | outer | inner => exact (outside edge).elim

/-- One outer visit precedes an infinite inner replay. Staging observes that
replay as divergence reached after a finite outer path. -/
theorem final_inner_replay :
    (tailGraph.inner inside).Infinite .outer ∧ tailGraph.Infinite .start ∧
      (tailGraph.outer inside).Finite .start false ∧
        ¬ (tailGraph.outer inside).Infinite .start := by
  have replay : (tailGraph.inner inside).Infinite .outer := by
    let path : Nat → Node
      | 0 => .outer
      | _ + 1 => .inner
    exact ⟨path, rfl, fun n => Nat.casesOn n ⟨rfl, rfl⟩ (fun _ => ⟨rfl, rfl⟩)⟩
  have segment : (tailGraph.outer inside).step .start .outer :=
    Graph.outer_step_iff.mpr ⟨(fun ⟨_, _, ub⟩ => ub), .start, .refl, rfl, by simp [inside]⟩
  have safe : ¬ tailGraph.ReachesUB .start := fun ⟨_, _, ub⟩ => ub
  refine ⟨replay, (Graph.infinite_outer_iff (inside := inside) safe).mpr ?_, ?_, ?_⟩
  · exact Or.inl ⟨.outer, .single segment, replay⟩
  · refine ⟨.outer, .single segment, Graph.ordinary_close_iff.mpr ?_⟩
    exact ⟨(fun ⟨_, _, ub⟩ => ub), Or.inr ⟨rfl, replay⟩⟩
  · rintro ⟨_, _, edges⟩
    have impossible := (tail_segment (edges 0)).2.symm.trans (tail_segment (edges 1)).1
    cases impossible

private def replayGraph : Graph Node Bool where
  step p q := match p with
    | .start | .outer => q = .inner
    | .inner => q = .outer
  ub _ := False
  finish p o := p = .outer ∧ o = true
  divergence := false

private theorem replay_segment {p : Node} (entry : replayGraph.step p .inner) :
    (replayGraph.outer inside).step p .outer :=
  Graph.outer_step_iff.mpr
    ⟨(fun ⟨_, _, ub⟩ => ub), .inner, .single ⟨entry, rfl⟩, rfl, by simp [inside]⟩

/-- Each outer visit consumes an inner-to-outer segment, even on the
outer self-edge. The infinite outer replay reflects flat divergence. -/
theorem infinitely_many_outer_visits :
    (replayGraph.outer inside).Infinite .start ∧ replayGraph.Infinite .start ∧
      ∀ q, ¬ (replayGraph.inner inside).Infinite q := by
  have replay : (replayGraph.outer inside).Infinite .start := by
    let path : Nat → Node
      | 0 => .start
      | _ + 1 => .outer
    exact ⟨path, rfl, fun n => Nat.casesOn n (replay_segment rfl) (fun _ => replay_segment rfl)⟩
  have safe : ¬ replayGraph.ReachesUB .start := fun ⟨_, _, ub⟩ => ub
  refine ⟨replay, (Graph.infinite_outer_iff (inside := inside) safe).mpr (Or.inr replay), ?_⟩
  rintro _ ⟨path, _, edges⟩
  have first : path 1 = .inner := (edges 0).2
  have second : replayGraph.step (path 1) (path 2) := (edges 1).1
  rw [first] at second
  have impossible := (show path 2 = .outer from second).symm.trans (edges 1).2
  cases impossible

theorem finite_external_return :
    replayGraph.Finite .start true ∧ (replayGraph.outer inside).Finite .start true := by
  have path : (replayGraph.outer inside).Reaches .start .outer := .single (replay_segment rfl)
  have finish : (replayGraph.inner inside).Finite .outer (.inr true) :=
    ⟨.outer, .refl, rfl, rfl⟩
  have safe : ¬ replayGraph.ReachesUB .start := fun ⟨_, _, ub⟩ => ub
  exact ⟨(Graph.finite_segmented_iff safe).mpr ⟨.outer, path, finish⟩,
    .outer, path, Graph.ordinary_close_iff.mpr ⟨(fun ⟨_, _, ub⟩ => ub), Or.inl finish⟩⟩

private abbrev I : List Unit := [()]
private abbrev O : List Unit := [()]
private abbrev L : List Unit := []

private abbrev innerIndex : Fin (I ++ O).length := ⟨0, by decide⟩
private abbrev outerIndex : Fin (I ++ O).length := ⟨1, by decide⟩

private abbrev jump (i : Fin (I ++ O).length) : Outcome ((I ++ O) ++ L).length Unit Unit :=
  .ret (internal (I ++ O) L i) .unit ()

private def ubRun : Run (I ++ O) L Unit Unit
  | .entry _ => ↑({o | o = jump innerIndex ∨ o = jump outerIndex} : Set (Outcome ((I ++ O) ++ L).length Unit Unit))
  | .block i _ _ => if i.val = 0 then ⊤ else ↑(∅ : Set (Outcome ((I ++ O) ++ L).length Unit Unit))

private abbrev ubGraph := Graph.ofRun ubRun
private abbrev insideBlock := insidePrefix (α := Unit) (σ := Unit) I O
private abbrev start : Point (I ++ O).length Unit Unit := .entry ()
private abbrev boundary : Point (I ++ O).length Unit Unit := .block outerIndex .unit ()

/-- An ordinary boundary transfer is available in the flat graph. The
competing inner UB takes priority, so staged feedback exposes fresh top. -/
theorem early_inner_ub :
    ubGraph.step start boundary ∧ ¬ (ubGraph.outer insideBlock).step start boundary ∧
      (ubGraph.outer insideBlock).close start = ⊤ ∧ close ubRun start = ⊤ := by
  have innerUB : (ubGraph.inner insideBlock).ReachesUB start := by
    refine ⟨.block innerIndex .unit (), .single ⟨?_, Nat.zero_lt_succ 0⟩, rfl⟩
    exact .branch ⟨WithTop.coe_ne_top, Or.inl rfl⟩
  have stagedTop : (ubGraph.outer insideBlock).close start = ⊤ :=
    Graph.close_top_iff.mpr ⟨start, .refl, Graph.close_top_iff.mpr innerUB⟩
  exact ⟨.branch ⟨WithTop.coe_ne_top, Or.inr rfl⟩,
    fun step => (Graph.outer_step_iff.mp step).1 innerUB,
    stagedTop, (close_two_levels ubRun start).symm.trans stagedTop⟩

#print axioms Graph.outer_step_progress
#print axioms Graph.reachesUB_outer_iff
#print axioms Graph.finite_segmented_iff
#print axioms Graph.infinite_outer_iff
#print axioms close_two_levels
#print axioms denote_feedback_two_levels
#print axioms final_inner_replay
#print axioms infinitely_many_outer_visits
#print axioms early_inner_ub

end LambdaSSAFeedbackEliminationRegression
