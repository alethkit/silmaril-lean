module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms

/-! Reentering a block can expose UB after an ordinary visit. An immediate
external exit bypasses a UB block. A native self-loop remains ordinary divergence. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback (Step Point Infinite ReachesUB)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSARegionUBFeedbackRegression

private abbrev τ := Ty Empty
private abbrev Γ : List τ := []
private abbrev unitLabel : List τ := [unit]

local instance : HasTy Empty τ := ⟨Empty.elim, Empty.elim⟩

private abbrev M : Model Empty 0 where
  α := Unit
  σ := Unit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound := Fin.elim0

private def exitEntry : Region Empty Γ (unitLabel ++ unitLabel) :=
  .native ⟨.br 1 .unit, .br rfl .unit⟩

private def deadBlock (i : Fin unitLabel.length) :
    Region Empty (unitLabel.get i :: Γ) (unitLabel ++ unitLabel) := .ub

/-- A UB block outside the reachable graph leaves the external return ordinary. -/
theorem unreachable_ub :
    (denote (.feedback exitEntry deadBlock) M ()).Ordinary (.ret 0 .unit ()) := by
  have noEdge (q : Point unitLabel.length Unit Unit) :
      ¬ Step (feedbackRun exitEntry deadBlock M) (.entry ()) q := by
    intro h
    cases h with
    | branch ret =>
      have run := ret.2
      change LambdaSSA.Semantics.Region.Eval M.instr (envOfBound M.bound)
        (.br 1 .unit) () (Feedback.internal unitLabel unitLabel _).val _ _ at run
      obtain rfl := Fin.eq_zero (by assumption : Fin 1)
      cases run
  have safe : ¬ ReachesUB (feedbackRun exitEntry deadBlock M) (.entry ()) := by
    rintro ⟨q, path, top⟩
    have eq := (Relation.reflTransGen_iff_eq noEdge).mp path
    subst q
    exact WithTop.coe_ne_top top
  apply Feedback.ordinary_close_iff.mpr
  exact ⟨safe, Or.inl ⟨.entry (), .refl, WithTop.coe_ne_top,
    LambdaSSA.Semantics.Region.Eval.br LambdaSSA.Semantics.Tm.Eval.unit⟩⟩

private def loopEntry : LambdaSSA.UB.Typed (Φ := Empty) Γ (unitLabel ++ []) :=
  ⟨.br 0 .unit, .br rfl .unit⟩

private def loopBlocks (i : Fin unitLabel.length) :
    LambdaSSA.UB.Typed (Φ := Empty) (unitLabel.get i :: Γ) (unitLabel ++ []) :=
  ⟨.br 0 (.var 0), by
    obtain rfl := Fin.eq_zero i
    exact .br rfl (.var rfl)⟩

private noncomputable abbrev loopGraph := feedbackRun (.native loopEntry) (fun i => .native (loopBlocks i)) M

/-- The entry starts an infinite internal replay, with no exposure of fresh UB. -/
theorem native_infinite_replay :
    Infinite loopGraph (.entry ()) ∧
      (denote (.feedback (.native loopEntry) (fun i => .native (loopBlocks i))) M ()).Ordinary .diverge := by
  have entryEdge : Step loopGraph (.entry ()) (.block 0 .unit ()) :=
    .branch ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Eval.br LambdaSSA.Semantics.Tm.Eval.unit⟩
  have backEdge : Step loopGraph (.block 0 .unit ()) (.block 0 .unit ()) :=
    .branch ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Eval.br LambdaSSA.Semantics.Tm.Eval.var⟩
  have infinite : Infinite loopGraph (.entry ()) := by
    let path : Nat → Point unitLabel.length Unit Unit
      | 0 => .entry ()
      | _ + 1 => .block 0 .unit ()
    exact ⟨path, rfl, fun j => Nat.casesOn j entryEdge (fun _ => backEdge)⟩
  refine ⟨infinite, ?_⟩
  rw [denote_native_feedback]
  exact ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.External.Diverges.of_internal
    (LambdaSSA.Semantics.cfg_self_loop _ _)⟩

/-- Finite closure alone misses the divergence of the native replay. -/
theorem finite_paths_miss_replay : ¬ Feedback.Finite loopGraph (.entry ()) .diverge := by
  rintro ⟨p, _, _, div⟩
  cases p with
  | entry s =>
    change LambdaSSA.Semantics.External.Diverges M.instr M.prim
      (.region (envOfBound M.bound) (.br 0 .unit) s) at div
    cases div.unfold with
    | core core => cases core
    | br arg => cases arg
  | block i a s =>
    change LambdaSSA.Semantics.External.Diverges M.instr M.prim
      (.region (envOfBound (extendModel M a).bound) (.br 0 (.var 0)) s) at div
    cases div.unfold with
    | core core => cases core
    | br arg => cases arg

private abbrev flag : τ := coprod unit unit
private abbrev flags : List τ := [flag]
private abbrev choices : List τ := [unit, unit]
private abbrev left : Value Unit := .inl .unit
private abbrev right : Value Unit := .inr .unit

private def flaggedEntry : Region Empty Γ (flags ++ []) :=
  .native ⟨.br 0 (.inl .unit), .br rfl (.inl .unit)⟩

private def dispatch : LambdaSSA.UB.Typed (Φ := Empty) [flag] choices :=
  ⟨.case (.var 0) (.br 0 .unit) (.br 1 .unit),
    .case (.var rfl) (.br rfl .unit) (.br rfl .unit)⟩

private def onChoice (i : Fin choices.length) : Region Empty (choices.get i :: [flag]) (flags ++ []) :=
  if i.val = 0 then .native ⟨.br 0 (.inr .unit), .br rfl (.inr .unit)⟩ else .ub

private def flaggedBlocks (i : Fin flags.length) :
    Region Empty (flags.get i :: Γ) (flags ++ []) :=
  Fin.cases (motive := fun i => Region Empty (flags.get i :: Γ) (flags ++ []))
    (.lsubst (.native dispatch) onChoice) (fun j => Fin.elim0 j) i

private noncomputable abbrev choiceView (a : Value Unit) :=
  denote (.native dispatch) (extendModel M a) ()

private noncomputable abbrev choiceAfter (a : Value Unit) (i : Fin choices.length)
    (payload : Value Unit) (mid : Unit) :=
  denote (onChoice i) (extendModel (extendModel M a) payload) mid

private theorem dispatch_left_label (i : Fin choices.length) (value : Value Unit) (mid : Unit)
    (result : Outcome.ret i value mid ∈ (choiceView left).possible) : i.val = 0 := by
  change LambdaSSA.Semantics.Region.Eval M.instr (envOfBound (extendModel M left).bound)
    (.case (.var 0) (.br 0 .unit) (.br 1 .unit)) () i.val value mid at result
  generalize i.val = label at result
  cases result with
  | case_inl _ branch =>
    cases branch
    rfl
  | case_inr arg _ => cases arg

private theorem flag_left_step :
    Step (feedbackRun flaggedEntry flaggedBlocks M) (.block 0 left ()) (.block 0 right ()) := by
  apply Step.branch
  change ((choiceView left).bind (choiceAfter left)).Ordinary _
  have safe : ¬ (choiceView left = ⊤ ∨
      ∃ i a s, Outcome.ret i a s ∈ (choiceView left).possible ∧ choiceAfter left i a s = ⊤) := by
    rintro (top | ⟨i, a, s, reached, top⟩)
    · exact WithTop.coe_ne_top top
    · have zero := dispatch_left_label i a s reached
      simp only [choiceAfter, onChoice, zero, ite_true, denote] at top
      exact WithTop.coe_ne_top top
  classical
  unfold Behaviour.bind
  rw [ite_eq_right safe]
  exact ⟨WithTop.coe_ne_top, Or.inr ⟨0, .unit, (), LambdaSSA.Semantics.Region.Eval.case_inl .var (.br .unit),
    LambdaSSA.Semantics.Region.Eval.br (.inr .unit)⟩⟩

private theorem flag_right_top :
    feedbackRun flaggedEntry flaggedBlocks M (.block 0 right ()) = ⊤ := by
  change (choiceView right).bind (choiceAfter right) = ⊤
  apply Behaviour.bind_eq_top_of_reaches_top (i := (1 : Fin 2)) (a := .unit) (s := ())
  · exact LambdaSSA.Semantics.Region.Eval.case_inr .var (.br .unit)
  · rfl

/-- The first visit to the block is ordinary. Its backedge changes the payload,
so the second visit reaches the UB continuation. -/
theorem ub_after_backedge : denote (.feedback flaggedEntry flaggedBlocks) M () = ⊤ := by
  have first : Step (feedbackRun flaggedEntry flaggedBlocks M) (.entry ()) (.block 0 left ()) :=
    .branch ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Eval.br (.inl .unit)⟩
  exact (denote_feedback_top_iff flaggedEntry flaggedBlocks M ()).mpr
    ⟨.block 0 right (), (Relation.ReflTransGen.single first).tail flag_left_step, flag_right_top⟩

#print axioms feedback_mono
#print axioms denote_feedback_top_iff
#print axioms denote_feedback_diverges_iff
#print axioms Feedback.close_ordinary_unfold
#print axioms Feedback.close_top_unfold
#print axioms denote_native_feedback
#print axioms ub_after_backedge
#print axioms unreachable_ub
#print axioms native_infinite_replay
#print axioms finite_paths_miss_replay

end LambdaSSARegionUBFeedbackRegression
