module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Delimiter.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Proofs

open Descent (BeforeReturn EarlierCallsReturn)
open Continuation.Feedback (atReturn)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ports final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {micro : Nat → Config m σ final} {begin : Nat}

private theorem no_return_at_entry {job : Job m ports} {frame : Stack m ports final}
    (entry : (micro begin).control = .eval job frame) :
    ¬ atReturn frame (micro begin).control := by
  rintro ⟨_, returned⟩
  rw [entry] at returned
  cases returned

private theorem first_pop {finish : Nat} {job : Job m ports} {frame : Stack m ports final}
    (entry : (micro begin).control = .eval job frame)
    (existsReturn : ∃ i, begin < i ∧ i < finish ∧ atReturn frame (micro i).control) :
    ∃ stop, begin < stop ∧ stop < finish ∧ atReturn frame (micro stop).control ∧
      BeforeReturn (fun j => (micro j).control) begin stop frame := by
  classical
  let stop := Nat.find existsReturn
  obtain ⟨after, before, returned⟩ := Nat.find_spec existsReturn
  refine ⟨stop, after, before, returned, fun i lower earlier popped => ?_⟩
  rcases Nat.eq_or_lt_of_le lower with same | later
  · subst i
    exact no_return_at_entry entry popped
  · exact Nat.find_min existsReturn earlier ⟨later, by omega, popped⟩

theorem first_child (steps : ∀ i, Step primitives (micro i) (micro (i + 1)))
    {caller : Entry m σ} {base : Stack m caller.call.results final}
    (entered : micro begin = caller.config base) (live : LiveFrom micro begin base)
    (existsChild : ∃ i, begin < i ∧ NonreturningCallAt micro i) :
    HasFirstChild primitives caller base micro begin := by
  classical
  let finish := Nat.find existsChild
  obtain ⟨after, child, stack, atChild, childLive⟩ := Nat.find_spec existsChild
  have earlier : EarlierFirstReturns micro (begin + 1) finish := by
    intro i lower upper params results callee arguments frame atCall
    have returned : ∃ j, i < j ∧ atReturn frame (micro j).control := by
      by_contra noReturn
      let earlierCall : Entry m σ := ⟨⟨results, ⟨params, callee, arguments⟩⟩, (micro i).store⟩
      have observed : micro i = earlierCall.config frame := by
        change micro i = Config.mk (.eval (.call callee arguments) frame) (micro i).store
        rw [← atCall]
      apply Nat.find_min existsChild upper
      refine ⟨by omega, earlierCall, frame, observed, fun j inTime popped => ?_⟩
      rcases Nat.eq_or_lt_of_le inTime with same | later
      · subst j
        exact no_return_at_entry atCall popped
      · exact noReturn ⟨j, later, popped⟩
    exact first_pop atCall (return_before_live steps upper atCall (congrArg Config.control atChild) childLive returned)
  have completed : EarlierCallsReturn (fun i => (micro i).control) (begin + 1) finish := by
    intro i lower upper params results callee arguments frame atCall
    obtain ⟨stop, later, before, popped, _⟩ := earlier i lower upper callee arguments frame atCall
    exact ⟨stop, later, before, popped⟩
  obtain ⟨pending, independent, observed⟩ :=
    entry_of_interval (fun i _ _ => steps i) entered atChild after (fun i lower _ => live i (by omega)) completed
  rw [← observed] at atChild childLive
  exact ⟨finish, child, pending, after, fun i later candidate => Nat.find_min' existsChild ⟨later, candidate⟩,
    atChild, childLive, earlier, independent⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Extraction.Proofs
