module

public import Mathlib.Data.Nat.Find
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {micro : Nat → State m final} {begin : Nat}

theorem return_or_live {job : Job m ports} {frame : Stack m ports final}
    (entered : micro begin = .eval job frame) :
    (∃ stop, begin < stop ∧ Feedback.atReturn frame (micro stop)) ∨ LiveFrom micro begin frame := by
  classical
  by_cases returned : ∃ stop, begin < stop ∧ Feedback.atReturn frame (micro stop)
  · exact .inl returned
  · refine .inr (fun i lower hit => ?_)
    rcases Nat.eq_or_lt_of_le lower with same | after
    · subst i
      obtain ⟨_, equal⟩ := hit
      rw [entered] at equal
      cases equal
    · exact returned ⟨i, after, hit⟩

theorem first_child (steps : ∀ i, Step (micro i) (micro (i + 1)))
    {caller : Entry m} {base : Stack m caller.results final}
    (entered : micro begin = caller.state base) (live : LiveFrom micro begin base)
    (existsChild : ∃ i, begin < i ∧ NonreturningCallAt micro i) :
    HasFirstChild caller base micro begin := by
  classical
  let finish := Nat.find existsChild
  obtain ⟨after, child, stack, atChild, childLive⟩ := Nat.find_spec existsChild
  have earlier : EarlierCallsReturn micro (begin + 1) finish := by
    intro i lower upper params results callee arguments frame atCall
    rcases return_or_live atCall with returned | stillLive
    · exact Feedback.return_before_live steps upper atCall atChild childLive returned
    · exact False.elim (Nat.find_min existsChild upper
        ⟨by omega, ⟨⟨results, ⟨params, callee, arguments⟩⟩, frame, atCall, stillLive⟩⟩)
  obtain ⟨pending, independent, observed⟩ :=
    entry_of_theta_interval steps entered atChild after (fun i lower _ => live i (by omega)) earlier
  rw [← observed] at atChild childLive
  exact ⟨finish, child, pending, after, atChild, childLive, earlier, independent⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Proofs
