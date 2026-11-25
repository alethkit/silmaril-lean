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

theorem step_deterministic {other : Config m σ final}
    (left : Step primitives source target) (right : Step primitives source other) : target = other :=
  _root_.Part.mem_unique left right

private theorem infinite_suffix (path : Relation.ReflTransGen (Step primitives) source target)
    (infinite : InfiniteTrace (Step primitives) source) : InfiniteTrace (Step primitives) target := by
  induction path with
  | refl => exact infinite
  | tail _ edge ih =>
    obtain ⟨next, picked, rest⟩ := ih.unfold
    exact step_deterministic picked edge ▸ rest

theorem no_infinite_of_reaches_blocked (path : Relation.ReflTransGen (Step primitives) source target)
    (blocked : target.Blocked primitives) : ¬ InfiniteTrace (Step primitives) source := by
  intro infinite
  obtain ⟨next, picked, _⟩ := (infinite_suffix path infinite).unfold
  change next ∈ target.next primitives at picked
  rw [blocked_next blocked] at picked
  exact _root_.Part.notMem_none _ picked

theorem no_blocked_liftTotal (source : Config m σ final) : ¬ source.Blocked (Primitives.liftTotal m σ) := by
  rintro ⟨active, _, undefined⟩
  exact _root_.Part.some_ne_none _ undefined

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Proofs
