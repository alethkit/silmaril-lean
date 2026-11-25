module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {source target : Config m σ final}

theorem pure_step (picked : source.next primitives = _root_.Part.some target) : Step primitives source target := by
  change target ∈ source.next primitives
  rw [picked]
  exact _root_.Part.mem_some _

theorem blocked_next (stopped : source.Blocked primitives) : source.next primitives = _root_.Part.none := by
  obtain ⟨active, selected, absent⟩ := stopped
  simp only [Config.next, selected, absent, _root_.Part.map_none]

theorem blocked_result (stopped : source.Blocked primitives) : source.result = none := by
  obtain ⟨active, selected, _⟩ := stopped
  cases source with
  | mk control store =>
    cases control with
    | eval => rfl
    | returned => cases selected

theorem next_liftTotal (source : Config m σ final) :
    source.next (Primitives.liftTotal m σ) =
      _root_.Part.ofOption (source.control.next.map fun next => ⟨next, source.store⟩) := by
  cases source with
  | mk control store =>
    cases control with
    | returned => rfl
    | eval job stack =>
      cases job with
      | call => rfl
      | region => rfl
      | iteration => rfl
      | node kind cs children input =>
        cases kind with
        | theta => rfl
        | base shape =>
          cases shape with
          | gamma => rfl
          | simple instruction => cases instruction <;> rfl

theorem step_liftTotal {source target : Config m σ final} :
    Step (Primitives.liftTotal m σ) source target ↔
      Continuation.Step source.control target.control ∧ source.store = target.store := by
  cases source with
  | mk control store =>
    cases target with
    | mk next finalStore =>
      change Config.mk next finalStore ∈ (Config.mk control store).next (Primitives.liftTotal m σ) ↔
        control.next = some next ∧ store = finalStore
      rw [next_liftTotal, _root_.Part.mem_ofOption]
      change control.next.map (fun next => Config.mk next store) = some (Config.mk next finalStore) ↔ _
      simp only [Option.map_eq_some_iff, Config.mk.injEq]
      constructor
      · rintro ⟨_, stepped, rfl, state⟩
        exact ⟨stepped, state⟩
      · rintro ⟨stepped, state⟩
        exact ⟨_, stepped, rfl, state⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs
