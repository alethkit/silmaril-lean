module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ}

theorem return_no_step (value : Tuple m.Val final) (store : σ) (target : Config m σ final) :
    ¬ Step primitives ⟨.returned value .halt, store⟩ target :=
  _root_.Part.notMem_none target

private theorem returned_of_result {control : State m final} {value : Tuple m.Val final}
    (result : control.result = some value) : control = .returned value .halt := by
  cases control with
  | eval => cases result
  | returned output stack =>
    cases stack with
    | halt => cases result; rfl
    | resume => cases result
    | loop => cases result

theorem progress (source : Config m σ final) :
    (∃ value, source.control = .returned value .halt) ∨ source.Blocked primitives ∨
      ∃ target, Step primitives source target := by
  cases selected : selectedPrimitive source.control with
  | some active =>
    rcases _root_.Part.eq_none_or_eq_some ((primitives.step active.site.opcode active.site.input).run source.store) with
      undefined | ⟨⟨output, store⟩, defined⟩
    · exact .inr (.inl ⟨active, selected, undefined⟩)
    · refine .inr (.inr ⟨⟨.returned output active.stack, store⟩, Step.of_next_some ?_⟩)
      simp only [Config.next, selected, defined, _root_.Part.map_some]
  | none =>
    cases next : source.control.next with
    | some control =>
      refine .inr (.inr ⟨⟨control, source.store⟩, Step.of_next_some ?_⟩)
      simp only [Config.next, selected, next]
      rfl
    | none =>
      cases result : source.control.result with
      | some value => exact .inl ⟨value, returned_of_result result⟩
      | none => exact False.elim (Continuation.no_unsupported source.control ⟨next, result⟩)

theorem no_step_iff (source : Config m σ final) :
    (∀ target, ¬ Step primitives source target) ↔
      (∃ value, source.control = .returned value .halt) ∨ source.Blocked primitives := by
  constructor
  · intro stopped
    rcases progress (primitives := primitives) source with returned | blocked | ⟨target, step⟩
    · exact .inl returned
    · exact .inr blocked
    · exact False.elim (stopped target step)
  · rintro (⟨value, returned⟩ | blocked)
    · have exactSource : source = ⟨.returned value .halt, source.store⟩ := by rw [← returned]
      intro target step
      exact return_no_step value source.store target (exactSource ▸ step)
    · exact fun _ => blocked.no_step

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Proofs
