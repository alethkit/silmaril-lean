module

public import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamily.Closure
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamilyProofs

open Continuation (State)
open Continuation.Partial (Config Primitives Step)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {final : Ports (Ty V S)} {familyL familyR : Family m} {primitives : Primitives m σ}
variable {a b : Config m σ final}

theorem positive_run {A : Type*} {R : A → A → Prop} {P : A → Prop} {start : A}
    (progress : ∀ x, P x → ∃ y, TransGen R x y ∧ P y) (initial : P start) :
    InfiniteTrace R start := by
  apply InfiniteTrace.coinduct (fun x => ∃ y, ReflTransGen R x y ∧ P y) ?_ ⟨start, .refl, initial⟩
  rintro x ⟨y, path, admitted⟩
  obtain ⟨z, positive, next⟩ := progress y admitted
  obtain ⟨first, step, rest⟩ := TransGen.head'_iff.mp (TransGen.trans_right path positive)
  exact ⟨first, step, z, rest, next⟩

private theorem result_no_step {source target : Config m σ final} {value : Tuple m.Val final} {store : σ}
    (result : source.result = some (value, store)) : ¬ Step primitives source target := by
  obtain ⟨control, initial⟩ := source
  cases control with
  | eval => cases result
  | returned values stack =>
    cases stack with
    | halt => exact _root_.Part.notMem_none _
    | resume => cases result
    | loop => cases result

private theorem no_step_of_block {a b : Config m σ final} (block : a.Blocked primitives) : ¬ Step primitives a b :=
  block.no_step

private theorem terminal_right {a b : Config m σ final} (paired : Advance primitives ids a b)
    (stop : ∀ target, ¬ Step primitives a target) : ∀ target, ¬ Step primitives b target := by
  intro target
  cases paired with
  | stepped path _ _ =>
    exact ((TransGen.head'_iff.mp path).elim (fun next h => stop next h.1)).elim
  | returned _ _ result => exact result_no_step result
  | blocked _ _ _ _ siteR _ _ undefinedR =>
    exact no_step_of_block ⟨_, siteR, undefinedR⟩

theorem one_or_terminal (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR)
    (pair : Admitted m ids familyL familyR a b) :
    (∃ a' b', TransGen (Step primitives) a a' ∧ TransGen (Step primitives) b b' ∧
      Admitted m ids familyL familyR a' b') ∨
    (Advance primitives ids a b ∧ ∀ target, ¬ Step primitives a target) := by
  have next := advance actions pair.live (dispatch_ready closed pair)
  cases next with
  | stepped pathL pathR live =>
    exact .inl ⟨_, _, pathL, pathR, live,
      closed_steps closed.closedL pair.memberL pathL.to_reflTransGen,
      closed_steps closed.closedR pair.memberR pathR.to_reflTransGen⟩
  | returned values resultL resultR =>
    exact .inr ⟨.returned values resultL resultR, fun _ => result_no_step resultL⟩
  | blocked opcode inputs frames siteL siteR store undefinedL undefinedR =>
    exact .inr ⟨.blocked opcode inputs frames siteL siteR store undefinedL undefinedR,
      fun _ => no_step_of_block ⟨_, siteL, undefinedL⟩⟩

private def ReachPair (primitives : Primitives m σ) (ids : GlobalRel)
    (familyL familyR : Family m) (initialL initialR curL curR : Config m σ final) : Prop :=
  ReflTransGen (Step primitives) initialL curL ∧ ReflTransGen (Step primitives) initialR curR ∧
    Admitted m ids familyL familyR curL curR

theorem paired_runs (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∃ endL endR, ReachedTerminal primitives ids a b endL endR) ∨
      (InfiniteTrace (Step primitives) a ∧ InfiniteTrace (Step primitives) b) := by
  classical
  by_cases terminates : ∃ endL endR, ReachedTerminal primitives ids a b endL endR
  · exact .inl terminates
  · right
    have next {x y : Config m σ final} (reached : ReachPair primitives ids familyL familyR a b x y) :
        ∃ x' y', TransGen (Step primitives) x x' ∧ TransGen (Step primitives) y y' ∧
          ReachPair primitives ids familyL familyR a b x' y' := by
      obtain ⟨pathL, pathR, live⟩ := reached
      rcases one_or_terminal actions closed live with ⟨x', y', stepL, stepR, later⟩ | terminal
      · exact ⟨x', y', stepL, stepR, pathL.trans stepL.to_reflTransGen, pathR.trans stepR.to_reflTransGen, later⟩
      · exact False.elim (terminates ⟨x, y, pathL, pathR, terminal⟩)
    constructor
    · apply positive_run (P := fun x => ∃ y, ReachPair primitives ids familyL familyR a b x y) ?_
        ⟨b, .refl, .refl, pair⟩
      rintro x ⟨y, reached⟩
      obtain ⟨x', y', stepL, _, later⟩ := next reached
      exact ⟨x', stepL, y', later⟩
    · apply positive_run (P := fun y => ∃ x, ReachPair primitives ids familyL familyR a b x y) ?_
        ⟨a, .refl, .refl, pair⟩
      rintro y ⟨x, reached⟩
      obtain ⟨x', y', _, stepR, later⟩ := next reached
      exact ⟨y', stepR, x', later⟩

private theorem infinite_suffix {source target : Config m σ final}
    (path : ReflTransGen (Step primitives) source target) (infinite : InfiniteTrace (Step primitives) source) :
    InfiniteTrace (Step primitives) target := by
  induction path with
  | refl => exact infinite
  | tail _ step ih =>
    obtain ⟨_, actual, tail⟩ := ih.unfold
    exact (_root_.Part.mem_unique actual step) ▸ tail

private theorem terminal_excludes_infinite {source target : Config m σ final}
    (path : ReflTransGen (Step primitives) source target) (stop : ∀ next, ¬ Step primitives target next) :
    ¬ InfiniteTrace (Step primitives) source := by
  intro run
  obtain ⟨next, actual, _⟩ := (infinite_suffix path run).unfold
  exact stop next actual

private theorem terminal_unique {source x y : Config m σ final}
    (first : ReflTransGen (Step primitives) source x) (second : ReflTransGen (Step primitives) source y)
    (stopX : ∀ next, ¬ Step primitives x next) (stopY : ∀ next, ¬ Step primitives y next) : x = y := by
  induction first using ReflTransGen.head_induction_on with
  | refl =>
    rcases ReflTransGen.cases_head second with same | ⟨next, picked, _⟩
    · exact same
    · exact False.elim (stopX next picked)
  | head step _ ih =>
    rcases ReflTransGen.cases_head second with rfl | ⟨next, picked, rest⟩
    · exact False.elim (stopY _ step)
    · exact ih ((_root_.Part.mem_unique picked step) ▸ rest)

theorem terminal_paths (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∀ endL, ReflTransGen (Step primitives) a endL → (∀ next, ¬ Step primitives endL next) →
      ∃ endR, ReachedTerminal primitives ids a b endL endR) ∧
    (∀ endR, ReflTransGen (Step primitives) b endR → (∀ next, ¬ Step primitives endR next) →
      ∃ endL, ReachedTerminal primitives ids a b endL endR) := by
  rcases paired_runs actions closed pair with ⟨x, y, pathL, pathR, terminal, stop⟩ | ⟨runL, runR⟩
  · have stopR := terminal_right terminal stop
    exact ⟨fun _ path halt => ⟨y, terminal_unique pathL path stop halt ▸ ⟨pathL, pathR, terminal, stop⟩⟩,
      fun _ path halt => ⟨x, terminal_unique pathR path stopR halt ▸ ⟨pathL, pathR, terminal, stop⟩⟩⟩
  · exact ⟨fun _ path halt => (terminal_excludes_infinite path halt runL).elim,
      fun _ path halt => (terminal_excludes_infinite path halt runR).elim⟩

theorem infinite_iff (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    InfiniteTrace (Step primitives) a ↔ InfiniteTrace (Step primitives) b := by
  rcases paired_runs actions closed pair with ⟨x, y, pathL, pathR, terminal, stop⟩ | ⟨runL, runR⟩
  · exact ⟨fun run => (terminal_excludes_infinite pathL stop run).elim,
      fun run => (terminal_excludes_infinite pathR (terminal_right terminal stop) run).elim⟩
  · exact ⟨fun _ => runR, fun _ => runL⟩

theorem returns (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∀ endL valueL store, ReflTransGen (Step primitives) a endL → endL.result = some (valueL, store) →
      ∃ endR valueR, ReflTransGen (Step primitives) b endR ∧ endR.result = some (valueR, store) ∧
        TupleRelated m ids valueL valueR) ∧
    (∀ endR valueR store, ReflTransGen (Step primitives) b endR → endR.result = some (valueR, store) →
      ∃ endL valueL, ReflTransGen (Step primitives) a endL ∧ endL.result = some (valueL, store) ∧
        TupleRelated m ids valueL valueR) := by
  obtain ⟨forward, reverse⟩ := terminal_paths actions closed pair
  constructor
  · intro endL valueL store path result
    obtain ⟨_, _, pathR, paired, _⟩ := forward endL path (fun _ => result_no_step result)
    cases paired with
    | stepped steps _ _ =>
      obtain ⟨_, step, _⟩ := TransGen.head'_iff.mp steps
      exact (result_no_step result step).elim
    | blocked _ _ _ siteL _ _ undefinedL _ =>
      have blocked : endL.Blocked primitives := ⟨_, siteL, undefinedL⟩
      simp [blocked.result_none] at result
    | returned related gotL gotR =>
      rw [result] at gotL
      cases gotL
      exact ⟨_, _, pathR, gotR, related⟩
  · intro endR valueR store path result
    obtain ⟨_, pathL, _, paired, _⟩ := reverse endR path (fun _ => result_no_step result)
    cases paired with
    | stepped _ steps _ =>
      obtain ⟨_, step, _⟩ := TransGen.head'_iff.mp steps
      exact (result_no_step result step).elim
    | blocked _ _ _ _ siteR _ _ undefinedR =>
      have blocked : endR.Blocked primitives := ⟨_, siteR, undefinedR⟩
      simp [blocked.result_none] at result
    | returned related gotL gotR =>
      rw [result] at gotR
      cases gotR
      exact ⟨_, _, pathL, gotL, related⟩

theorem blocks (actions : ActionsRespect primitives ids)
    (closed : ClosedFamily primitives ids familyL familyR) (pair : Admitted m ids familyL familyR a b) :
    (∀ endL, ReflTransGen (Step primitives) a endL → endL.Blocked primitives →
      ∃ endR, ReachedTerminal primitives ids a b endL endR ∧ endR.Blocked primitives) ∧
    (∀ endR, ReflTransGen (Step primitives) b endR → endR.Blocked primitives →
      ∃ endL, ReachedTerminal primitives ids a b endL endR ∧ endL.Blocked primitives) := by
  obtain ⟨forward, reverse⟩ := terminal_paths actions closed pair
  constructor
  · intro endL path blocked
    obtain ⟨endR, reached⟩ := forward endL path (fun _ => blocked.no_step)
    refine ⟨endR, reached, ?_⟩
    cases reached.2.2.1 with
    | stepped steps _ _ =>
      obtain ⟨_, step, _⟩ := TransGen.head'_iff.mp steps
      exact (blocked.no_step step).elim
    | returned _ result _ => simp [blocked.result_none] at result
    | blocked _ _ _ _ site _ _ undefined => exact ⟨_, site, undefined⟩
  · intro endR path blocked
    obtain ⟨endL, reached⟩ := reverse endR path (fun _ => blocked.no_step)
    refine ⟨endL, reached, ?_⟩
    cases reached.2.2.1 with
    | stepped _ steps _ =>
      obtain ⟨_, step, _⟩ := TransGen.head'_iff.mp steps
      exact (blocked.no_step step).elim
    | returned _ _ result => simp [blocked.result_none] at result
    | blocked _ _ _ site _ _ undefined _ => exact ⟨_, site, undefined⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.ClosedFamilyProofs
