module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs

open Continuation.Feedback (atReturn)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

theorem advance (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {i : Nat} {source target : Config m σ final}
    (entered : micro i = source) (edge : Step primitives source target) : micro (i + 1) = target :=
  _root_.Part.mem_unique (steps i) (entered.symm ▸ edge)

private theorem delimited_slice (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    (frame : Stack m ports final) (count : Nat)
    (inside : ∀ offset, offset < count → ¬ atReturn frame (micro (begin + offset)).control) :
    ReflTransGen (InsideStep primitives frame) (micro begin) (micro (begin + count)) := by
  induction count with
  | zero => exact .refl
  | succ count ih =>
    exact (ih fun offset smaller => inside offset (by omega)).tail
      ⟨steps (begin + count), inside count (Nat.lt_succ_self _)⟩

theorem return_or_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {job : Job m ports} {frame : Stack m ports final} {store : σ}
    (entered : micro begin = ⟨.eval job frame, store⟩) :
    (∃ stop, begin ≤ stop ∧ ∃ value, micro stop = ⟨.returned value frame, (micro stop).store⟩ ∧
      Eval primitives job store (.returned value (micro stop).store)) ∨ LiveFrom micro begin frame := by
  classical
  by_cases found : ∃ offset, atReturn frame (micro (begin + offset)).control
  · let offset := Nat.find found
    obtain ⟨value, returned⟩ := Nat.find_spec found
    have arrived : micro (begin + offset) = ⟨.returned value frame, (micro (begin + offset)).store⟩ := by
      rw [← returned]
    have path := delimited_slice (begin := begin) steps frame offset
      (fun i smaller => Nat.find_min found smaller)
    rw [entered, arrived] at path
    exact .inl ⟨_, Nat.le_add_right _ _, value, arrived, returns_of_delimited frame path⟩
  · refine .inr (fun i lower returned => found ⟨i - begin, ?_⟩)
    simpa only [Nat.add_sub_of_le lower] using returned

variable {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
variable {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
variable {parent : Stack m carried final} {input : Tuple m.Val carried × σ}

private abbrev restart (body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried))
    (parent : Stack m carried final) (input : Tuple m.Val carried × σ) : Config m σ final :=
  (Feedback.Restart.mk carried sigs body input).config parent

private theorem enter_body (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    (entered : micro begin = restart body parent input) :
    micro (begin + 1) = ⟨.eval (.region body input.1 PUnit.unit) (.loop body parent), input.2⟩ :=
  advance steps entered (.of_next_some rfl)

private theorem feedback_or_live (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    (entered : micro begin = restart body parent input) (live : LiveFrom micro begin parent) :
    (∃ stop next, begin < stop ∧ micro stop = restart body parent next ∧ Feedback.Iteration primitives body input next) ∨
      LiveFrom micro (begin + 1) (.loop body parent) := by
  rcases return_or_live steps (enter_body steps entered) with ⟨stop, later, value, returned, ran⟩ | stillLive
  · cases value with
    | cons tag values =>
      have feedback : (tag.selector.val == 1) = true := by
        by_contra exits
        have edge : Step primitives ⟨.returned (.cons tag values) (.loop body parent), (micro stop).store⟩
            ⟨.returned values parent, (micro stop).store⟩ := by
          apply Step.of_next_some
          change _root_.Part.some (Config.mk (State.finishLoop body tag values parent) (micro stop).store) = _
          rw [State.finishLoop, ite_eq_right exits]
        exact live (stop + 1) (by omega) ⟨values, congrArg Config.control (advance steps returned edge)⟩
      let next := (values, (micro stop).store)
      have edge : Step primitives ⟨.returned (.cons tag values) (.loop body parent), (micro stop).store⟩
          (restart body parent next) := by
        apply Step.of_next_some
        change _root_.Part.some (Config.mk (State.finishLoop body tag values parent) (micro stop).store) = _
        rw [State.finishLoop, ite_eq_left feedback]
        rfl
      exact .inl ⟨stop + 1, next, by omega, advance steps returned edge, tag, ran, feedback⟩
  · exact .inr stillLive

theorem loop_or_live_body (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    (entered : micro begin = (Feedback.Restart.mk carried sigs body input).config parent)
    (live : LiveFrom micro begin parent) :
    (∃ positions inputs, positions 0 = begin ∧
      FeedbackOnStream primitives micro ⟨carried, sigs, body, input⟩ parent positions inputs) ∨
      ∃ (i : Nat) (current : Tuple m.Val carried × σ), begin < i ∧
        ReflTransGen (Feedback.Iteration primitives body) input current ∧
        micro i = ⟨.eval (.region body current.1 PUnit.unit) (.loop body parent), current.2⟩ ∧
        LiveFrom micro i (.loop body parent) := by
  classical
  let seen (p : Nat × (Tuple m.Val carried × σ)) : Prop :=
    begin ≤ p.1 ∧ micro p.1 = restart body parent p.2 ∧ ReflTransGen (Feedback.Iteration primitives body) input p.2
  by_cases bodyLive : ∃ p, seen p ∧ LiveFrom micro (p.1 + 1) (.loop body parent)
  · obtain ⟨⟨i, current⟩, ⟨lower, observed, completed⟩, stillLive⟩ := bodyLive
    exact .inr ⟨i + 1, current, by omega, completed, enter_body steps observed, stillLive⟩
  · let advances (p q : Nat × (Tuple m.Val carried × σ)) : Prop :=
      p.1 < q.1 ∧ Feedback.Iteration primitives body p.2 q.2 ∧ seen p
    have infinite : InfiniteTrace advances (begin, input) := by
      apply InfiniteTrace.coinduct seen ?_ ⟨Nat.le_refl _, entered, .refl⟩
      rintro ⟨i, current⟩ ⟨lower, observed, completed⟩
      rcases feedback_or_live steps observed (fun j after => live j (lower.trans after)) with
        ⟨stop, next, later, atNext, iteration⟩ | stillLive
      · exact ⟨(stop, next), ⟨later, iteration, lower, observed, completed⟩,
          by omega, atNext, completed.tail iteration⟩
      · exact False.elim (bodyLive ⟨(i, current), ⟨lower, observed, completed⟩, stillLive⟩)
    obtain ⟨visits, first, edges⟩ := infinite
    refine .inl ⟨fun n => (visits n).1, fun n => (visits n).2, congrArg Prod.fst first, ?_⟩
    refine ⟨congrArg Prod.snd first, ?_, fun n => (edges n).1, fun n => (edges n).2.2.2.1, fun n => (edges n).2.1⟩
    simpa only [first] using live

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Theta.Proofs
