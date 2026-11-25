module

public import Silmaril.Foundations.InfiniteTrace.Deterministic
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Progress

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Proofs

open CallDescent (Entry)
open Relation (ReflTransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {final : Ports (Ty V S)}
variable {primitives : Primitives m σ} {entry : Entry m σ}

private theorem unique_step : Relator.RightUnique (Step (final := final) primitives) :=
  fun _ _ _ left right => _root_.Part.mem_unique left right

private theorem exhaustive :
    Returns primitives entry ∨ Blocks primitives entry ∨ Divergence.Diverges primitives entry := by
  classical
  by_cases returned : Returns primitives entry
  · exact .inl returned
  by_cases blocked : Blocks primitives entry
  · exact .inr (.inl blocked)
  refine .inr (.inr (Divergence.diverges_iff_infinite.mpr ?_))
  apply InfiniteTrace.coinduct (ReflTransGen (Step primitives) (entry.config .halt)) ?_ .refl
  intro source path
  rcases progress (primitives := primitives) source with ⟨value, control⟩ | stuck | ⟨target, step⟩
  · have exactSource : source = ⟨.returned value .halt, source.store⟩ := by rw [← control]
    exact False.elim (returned ⟨value, source.store, returns_iff_path.mpr (exactSource ▸ path)⟩)
  · obtain ⟨site, pending, evaluation, _⟩ := blocked_iff_path.mpr ⟨path, stuck⟩
    exact False.elim (blocked ⟨site, pending, source.store, evaluation⟩)
  · exact ⟨target, step, path.tail step⟩

private theorem return_exclusive (normal : Returns primitives entry) :
    ¬ Blocks primitives entry ∧ ¬ Divergence.Diverges primitives entry := by
  obtain ⟨value, finalStore, returned⟩ := normal
  have path := returned.steps (Stack.halt : Stack m entry.call.results entry.call.results)
  constructor
  · rintro ⟨site, pending, store, blocked⟩
    have stopped := blocked.blocks (Stack.halt : Stack m entry.call.results entry.call.results)
    have same := RightUnique.reach_final_eq unique_step path (blocked.steps .halt)
      (return_no_step value finalStore) (fun _ => stopped.no_step)
    cases same
  · intro diverges
    exact RightUnique.not_infinite_of_final unique_step path (return_no_step value finalStore)
      (Divergence.diverges_iff_infinite.mp diverges)

private theorem block_excludes_divergence (stopped : Blocks primitives entry) :
    ¬ Divergence.Diverges primitives entry := by
  obtain ⟨_, _, _, blocked⟩ := stopped
  exact Divergence.not_diverges_of_blocked (blocked.steps .halt) (blocked.blocks .halt)

theorem trichotomy : Trichotomy primitives entry :=
  ⟨exhaustive, return_exclusive, block_excludes_divergence⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Proofs
