module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Classification.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Divergence.Thms
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Proofs

open Continuation.Partial

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {results : Ports (Ty V S)}
variable {request : Request m σ results} {primitives : Primitives m σ}
variable {exports : Tuple m.Val request.exports} {store : σ} {failure : Failure m σ}

private theorem link_exists : ∃ outcome, request.Links primitives outcome :=
  PartialLink.exists_outcome

private theorem canonical_eq {outcome : PartialLink.Outcome m σ request.exports}
    (linked : request.Links primitives outcome) :
    PartialLink.link primitives request.unitId request.graph request.imported request.initialStore = outcome :=
  PartialLink.outcome_unique PartialLink.link_spec linked

theorem start_linked (linked : request.Links primitives (.linked exports store)) :
    request.start primitives =
      .ok ⟨Continuation.start (.call (exports.get request.port) request.arguments), store⟩ := by
  change request.start primitives = .ok ((request.entry exports store).config .halt)
  simp only [Request.start, canonical_eq linked]

private theorem start_undefined (blocked : request.Links primitives (.undefined failure)) :
    request.start primitives = .error failure := by
  simp only [Request.start, canonical_eq blocked]

private theorem no_success_of_undefined {observes : Tuple m.Val request.exports → σ → Prop}
    (blocked : request.LinkBlocks primitives) : ¬ request.AfterLink primitives observes := by
  rintro ⟨exports, store, linked, _⟩
  obtain ⟨_, failed⟩ := blocked
  cases PartialLink.outcome_unique linked failed

private theorem afterLink_iff {observes : Tuple m.Val request.exports → σ → Prop}
    (linked : request.Links primitives (.linked exports store)) :
    request.AfterLink primitives observes ↔ observes exports store := by
  constructor
  · rintro ⟨_, _, other, observed⟩
    obtain ⟨rfl, rfl⟩ := PartialLink.Outcome.linked.inj (PartialLink.outcome_unique other linked)
    exact observed
  · exact fun observed => ⟨exports, store, linked, observed⟩

theorem start_error_iff :
    request.start primitives = .error failure ↔ request.Links primitives (.undefined failure) := by
  refine ⟨?_, start_undefined⟩
  intro failed
  obtain ⟨outcome, evaluated⟩ := link_exists (request := request) (primitives := primitives)
  cases outcome with
  | undefined actual =>
    have equal : actual = failure := Except.error.inj ((start_undefined evaluated).symm.trans failed)
    exact equal ▸ evaluated
  | linked =>
    cases (start_linked evaluated).symm.trans failed

private theorem afterLink_iff_start {observes : Config m σ results → Prop} :
    request.AfterLink primitives (fun exports store => observes ((request.entry exports store).config .halt)) ↔
      ∃ config, request.start primitives = .ok config ∧ observes config := by
  constructor
  · rintro ⟨exports, store, linked, observed⟩
    exact ⟨_, start_linked linked, observed⟩
  · rintro ⟨config, started, observed⟩
    obtain ⟨outcome, evaluated⟩ := link_exists (request := request) (primitives := primitives)
    cases outcome with
    | undefined =>
      have equal := (start_undefined evaluated).symm.trans started
      cases equal
    | linked exports store =>
      have equal : (request.entry exports store).config .halt = config :=
        Except.ok.inj ((start_linked evaluated).symm.trans started)
      exact ⟨exports, store, evaluated, Eq.mpr (congrArg observes equal) observed⟩

theorem outcomes : Outcomes request primitives := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨outcome, linked⟩ := link_exists (request := request) (primitives := primitives)
    cases outcome with
    | undefined => exact .inl ⟨_, linked⟩
    | linked exports store =>
      rcases (Classification.trichotomy (primitives := primitives)
        (entry := request.entry exports store)).exhaustive with returned | blocked | divergent
      · exact .inr (.inl ⟨_, _, linked, returned⟩)
      · exact .inr (.inr (.inl ⟨_, _, linked, blocked⟩))
      · exact .inr (.inr (.inr ⟨_, _, linked, divergent⟩))
  · intro blocked
    exact ⟨no_success_of_undefined blocked, no_success_of_undefined blocked, no_success_of_undefined blocked⟩
  · rintro ⟨exports, store, linked, returned⟩
    rw [Request.Blocks, Request.Diverges, afterLink_iff linked, afterLink_iff linked]
    exact (Classification.trichotomy (entry := request.entry exports store)).return_exclusive returned
  · rintro ⟨exports, store, linked, blocked⟩
    rw [Request.Diverges, afterLink_iff linked]
    exact (Classification.trichotomy (entry := request.entry exports store)).block_excludes_divergence blocked

theorem returns_iff_machine :
    request.Returns primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        ∃ value finalStore, Relation.ReflTransGen (Step primitives) source ⟨.returned value .halt, finalStore⟩ := by
  rw [← afterLink_iff_start]
  constructor
  · rintro ⟨exports, store, linked, value, finalStore, returned⟩
    exact ⟨exports, store, linked, value, finalStore, returns_iff_path.mp returned⟩
  · rintro ⟨exports, store, linked, value, finalStore, path⟩
    exact ⟨exports, store, linked, value, finalStore, returns_iff_path.mpr path⟩

theorem blocks_iff_machine :
    request.Blocks primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        ∃ target, Relation.ReflTransGen (Step primitives) source target ∧ target.Blocked primitives := by
  rw [← afterLink_iff_start]
  constructor
  · rintro ⟨exports, store, linked, site, pending, stopped, blocked⟩
    exact ⟨exports, store, linked, _, blocked.steps .halt, blocked.blocks .halt⟩
  · rintro ⟨exports, store, linked, target, path, blocked⟩
    obtain ⟨site, pending, evaluation, _⟩ := blocked_iff_path.mpr ⟨path, blocked⟩
    exact ⟨exports, store, linked, site, pending, target.store, evaluation⟩

theorem diverges_iff_machine :
    request.Diverges primitives ↔
      ∃ source : Config m σ results, request.start primitives = .ok source ∧
        InfiniteTrace (Step primitives) source := by
  rw [← afterLink_iff_start]
  exact ⟨fun ⟨exports, store, linked, divergent⟩ =>
    ⟨exports, store, linked, Divergence.diverges_iff_infinite.mp divergent⟩,
    fun ⟨exports, store, linked, infinite⟩ =>
    ⟨exports, store, linked, Divergence.diverges_iff_infinite.mpr infinite⟩⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Invocation.Proofs
