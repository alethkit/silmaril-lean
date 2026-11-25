module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Proofs

open Descent (Pending stackDepth)
open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {primitives : Primitives m σ} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {store : σ} {next : Entry m σ} {pending : Pending m next.call.results ports}

theorem prefix_steps (reached : Prefix primitives job store next pending) (stack : Stack m ports final) :
    TransGen (Step primitives) ⟨.eval job stack, store⟩ (next.config (pending.push stack)) := by
  induction reached with
  | apply => exact .single (.of_next_some rfl)
  | @later args head ports past tail node children rest entry locals value store middle next pending returned _ ih =>
    let saved := Stack.resume rest entry locals stack
    have entered : Step primitives ⟨.eval (.region (.bind node children rest) entry locals) stack, store⟩
        ⟨.eval (.node node.kind node.childSigs children (node.inputs.read entry locals)) saved, store⟩ :=
      .of_next_some rfl
    have resumed : Step primitives ⟨.returned value saved, middle⟩
        ⟨.eval (.region rest entry (locals.snoc value)) stack, middle⟩ := .of_next_some rfl
    exact TransGen.trans_right (((returned.steps saved).head entered).tail resumed) (ih stack)
  | @inside args head ports past tail node children rest entry locals store next pending _ ih =>
    exact (ih (.resume rest entry locals stack)).head (.of_next_some rfl)
  | gamma _ ih => exact (ih stack).head (.of_next_some rfl)
  | theta _ ih => exact (ih stack).head (.of_next_some rfl)
  | @iteration carried sigs body input current next pending completed _ ih =>
    have entered : Step primitives (Feedback.Restart.config ⟨carried, sigs, body, current⟩ stack)
        ⟨.eval (.region body current.1 PUnit.unit) (.loop body stack), current.2⟩ := .of_next_some rfl
    have feedback := (Feedback.Reaches.restart completed).steps stack
    exact TransGen.trans_right (feedback.tail entered) (ih (.loop body stack))

theorem entry_steps {entry : Entry m σ} {pending : Pending m next.call.results entry.call.results}
    (reached : Prefix primitives entry.call.openBody entry.store next pending)
    (stack : Stack m entry.call.results final) :
    TransGen (Step primitives) (entry.config stack) (next.config (pending.push stack)) :=
  (prefix_steps reached stack).head (.of_next_some rfl)

private def isRegion : Job m ports → Prop
  | .region .. => True
  | _ => False

private theorem positive_depth (reached : Prefix primitives job store next pending) (region : isRegion job) :
    0 < pending.depth := by
  induction reached with
  | apply => cases region
  | later _ _ ih => exact ih trivial
  | inside => exact Nat.succ_pos _
  | gamma => cases region
  | theta => cases region
  | iteration => cases region

private theorem depth_push {selected : Ports (Ty V S)} (pending : Pending m selected ports)
    (stack : Stack m ports final) : stackDepth (pending.push stack) = stackDepth stack + pending.depth := by
  induction pending with
  | empty => rfl
  | bind suffix entry locals inside ih =>
    change stackDepth (inside.push (.resume suffix entry locals stack)) = stackDepth stack + (inside.depth + 1)
    rw [ih]
    change (stackDepth stack + 1) + inside.depth = _
    omega
  | loop body inside ih =>
    change stackDepth (inside.push (.loop body stack)) = stackDepth stack + (inside.depth + 1)
    rw [ih]
    change (stackDepth stack + 1) + inside.depth = _
    omega

theorem stack_grows (run : Run primitives) (base : Stack m (run.entry 0).call.results final) (n : Nat) :
    stackDepth (run.stackAt base n) < stackDepth (run.stackAt base (n + 1)) := by
  rw [Run.stackAt, depth_push]
  exact Nat.lt_add_of_pos_right (positive_depth (run.reaches n) trivial)

private theorem infinite_of_segments (boundary : Nat → Config m σ final)
    (segments : ∀ n, TransGen (Step primitives) (boundary n) (boundary (n + 1))) :
    InfiniteTrace (Step primitives) (boundary 0) := by
  apply InfiniteTrace.coinduct (fun state => ∃ i, TransGen (Step primitives) state (boundary i)) ?_
    ⟨1, segments 0⟩
  rintro state ⟨i, path⟩
  obtain ⟨next, edge, later⟩ := TransGen.head'_iff.mp path
  refine ⟨next, edge, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp later with same | remaining
  · subst next
    exact ⟨i + 1, segments i⟩
  · exact ⟨i, remaining⟩

private theorem position_of_path {micro : Nat → Config m σ final} {i : Nat} {target : Config m σ final}
    (steps : ∀ j, Step primitives (micro j) (micro (j + 1)))
    (path : ReflTransGen (Step primitives) (micro i) target) :
    ∃ count : Nat, micro (i + count) = target := by
  induction path with
  | refl => exact ⟨0, rfl⟩
  | tail _ edge ih =>
    obtain ⟨count, reached⟩ := ih
    refine ⟨count + 1, ?_⟩
    rw [Nat.add_succ]
    exact _root_.Part.mem_unique (steps (i + count)) (reached.symm ▸ edge)

private theorem next_position {micro : Nat → Config m σ final} {i : Nat} {target : Config m σ final}
    (steps : ∀ j, Step primitives (micro j) (micro (j + 1)))
    (path : TransGen (Step primitives) (micro i) target) :
    ∃ j, i < j ∧ micro j = target := by
  obtain ⟨before, more, edge⟩ := TransGen.tail'_iff.mp path
  obtain ⟨count, reached⟩ := position_of_path steps more
  exact ⟨i + count + 1, by omega, _root_.Part.mem_unique (steps (i + count)) (reached.symm ▸ edge)⟩

theorem checkpoints (run : Run primitives) (base : Stack m (run.entry 0).call.results final) :
    ∃ micro positions, Checkpoints run base micro positions := by
  classical
  let boundary (n : Nat) := (run.entry n).config (run.stackAt base n)
  have segments (n : Nat) : TransGen (Step primitives) (boundary n) (boundary (n + 1)) :=
    entry_steps (run.reaches n) (run.stackAt base n)
  obtain ⟨micro, initial, steps⟩ := infinite_of_segments boundary segments
  let extend (n : Nat) (i : {i // micro i = boundary n}) : {j // i.val < j ∧ micro j = boundary (n + 1)} :=
    Classical.indefiniteDescription _ (next_position steps (i.property.symm ▸ segments n))
  let index : (n : Nat) → {i // micro i = boundary n} :=
    Nat.rec ⟨0, initial⟩ fun n i => ⟨(extend n i).val, (extend n i).property.2⟩
  exact ⟨micro, fun n => (index n).val, rfl, steps,
    fun n => (extend n (index n)).property.1, fun n => (index n).property⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.CallDescent.Proofs
