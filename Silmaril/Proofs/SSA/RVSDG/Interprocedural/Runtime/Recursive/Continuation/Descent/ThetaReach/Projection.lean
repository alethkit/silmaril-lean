module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Reflection

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs

open Completeness

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {final : Ports (Ty V S)}
variable {micro : Nat → State m final}

private theorem prepend_calls {parent child : Global.Point m final}
    (path : Relation.ReflTransGen (Global.ChildStep micro) parent child)
    (ending : FeedbackRoute m child.entry child.stack) : FeedbackRoute m parent.entry parent.stack := by
  refine path.head_induction_on (motive := fun p _ => FeedbackRoute m p.entry p.stack) ending ?_
  intro current next edge _ suffix
  obtain ⟨_, observed, frames⟩ := edge
  rw [← frames] at suffix
  exact .call observed.reaches suffix

theorem feedback_of_observation {root : Entry m} {micro : Nat → State m root.results}
    (steps : ∀ i, Step (micro i) (micro (i + 1))) (observed : Global.FeedbackAfterCalls root micro) :
    FeedbackRoute m root .halt := by
  obtain ⟨last, path, live, closed, feedback⟩ := observed
  obtain ⟨i, carried, sigs, body, parent, inputs, positions, after, loopLive, trace⟩ := feedback
  let target : Restart m := ⟨carried, sigs, body, inputs 0⟩
  have selected : micro i = target.state parent := by
    change micro i = Feedback.restart body parent (inputs 0)
    simpa only [trace.first, Nat.add_zero] using trace.atRestart 0
  have earlier : EarlierCallsReturn micro (last.index + 1) i := by
    intro j lower upper params results callee arguments frame atCall
    rcases Completeness.return_or_live atCall with returned | liveCall
    · exact Feedback.return_before_live steps upper atCall selected loopLive returned
    · exact False.elim (closed j (by omega) ⟨⟨results, ⟨params, callee, arguments⟩⟩, frame, atCall, liveCall⟩)
  have enter : Step last.state (.eval last.entry.openBody last.stack) := rfl
  have opened : micro (last.index + 1) = .eval last.entry.openBody last.stack :=
    step_deterministic (steps last.index) (live.1.symm ▸ enter)
  obtain ⟨pending, reached, _⟩ := reaches_of_interval steps opened selected after
    (fun j lower _ => live.2 j (by omega)) earlier
  have productive : Feedback.Run target.body target.input :=
    Feedback.run_iff_restarts.mpr ⟨inputs, (fun n => micro (i + n)), positions, rfl, trace⟩
  exact prepend_calls path (.restart reached productive)

private theorem read_entry {entry : Entry m} (stack : Stack m entry.results final) :
    Entry.ofState (entry.state stack) = some entry := by
  cases entry with
  | mk results activation => cases activation; rfl

theorem diverges_complete {root : Entry m} (trace : InfiniteTrace Step (root.state .halt)) : Diverges root := by
  obtain ⟨micro, initial, steps⟩ := trace
  rcases Global.classify_root steps initial with chain | feedback
  · obtain ⟨run, base, _, same, _⟩ := Global.chain_checkpoints steps initial chain
    have sameEntry := congrArg Entry.ofState same
    rw [read_entry base, read_entry (.halt : Stack m root.results root.results)] at sameEntry
    exact .inl ⟨run, Option.some.inj sameEntry⟩
  · exact .inr (feedback_of_observation steps feedback)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Proofs
