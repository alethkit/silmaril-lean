module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Proofs

open Relation (ReflTransGen TransGen)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {ports final : Ports (Ty V S)}
variable {job : Job m ports} {next : Entry m} {pending : Pending m next.results ports}

private theorem feedback_steps {carried : Ports (Ty V S)} {sigs : List (Ports (Ty V S))}
    {body : NestedTheta.Term (Instruction Op) carried [] sigs (Theta.BodyResults carried)}
    {input current : Tuple m.Val carried}
    (completed : ReflTransGen (Feedback.Iteration body) input current) (stack : Stack m carried final) :
    ReflTransGen Step (Feedback.restart body stack input) (Feedback.restart body stack current) := by
  induction completed with
  | refl => exact .refl
  | tail _ iteration ih =>
    exact ih.trans (Feedback.segment_steps (Feedback.iteration_iff_segment.mp iteration)).to_reflTransGen

theorem prefix_steps (reached : Prefix m job next pending) (stack : Stack m ports final) :
    TransGen Step (.eval job stack) (next.state (pending.push stack)) := by
  induction reached with
  | apply => exact .single rfl
  | @later args head ports past tail node children rest entry locals value next pending returned reached ih =>
    let frame := Stack.resume rest entry locals stack
    have completed := (Feedback.returns_iff_delimited frame).mp returned
    have ordinary := ReflTransGen.mono (fun _ _ (edge : Feedback.InsideStep frame _ _) => edge.1) _ _ completed
    have entered : Step (.eval (.region (.bind node children rest) entry locals) stack)
        (.eval (.node node.kind node.childSigs children (node.inputs.read entry locals)) frame) := rfl
    have resumed : Step (.returned value frame) (.eval (.region rest entry (locals.snoc value)) stack) := rfl
    exact TransGen.trans_right ((ordinary.head entered).tail resumed) (ih stack)
  | @inside args head ports past tail node children rest entry locals next pending reached ih =>
    exact (ih (.resume rest entry locals stack)).head rfl
  | gamma selected ih => exact (ih stack).head rfl
  | theta _ ih => exact (ih stack).head rfl
  | @iteration carried sigs body input current next pending completed active ih =>
    have enter : Step (Feedback.restart body stack current)
        (.eval (.region body current PUnit.unit) (.loop body stack)) := rfl
    exact TransGen.trans_right ((feedback_steps completed stack).tail enter) (ih (.loop body stack))

theorem entry_steps {entry : Entry m} {pending : Pending m next.results entry.results}
    (reached : Prefix m entry.openBody next pending) (stack : Stack m entry.results final) :
    TransGen Step (entry.state stack) (next.state (pending.push stack)) :=
  (prefix_steps reached stack).head (show Step (entry.state stack) (.eval entry.openBody stack) from rfl)

theorem depth_push {selected : Ports (Ty V S)} (pending : Pending m selected ports) (stack : Stack m ports final) :
    stackDepth (pending.push stack) = stackDepth stack + pending.depth := by
  induction pending with
  | empty => rfl
  | bind suffix entry locals inside ih =>
    change stackDepth (inside.push (.resume suffix entry locals stack)) =
      stackDepth stack + (inside.depth + 1)
    rw [ih]
    change (stackDepth stack + 1) + inside.depth = _
    omega
  | loop body inside ih =>
    change stackDepth (inside.push (.loop body stack)) = stackDepth stack + (inside.depth + 1)
    rw [ih]
    change (stackDepth stack + 1) + inside.depth = _
    omega

private def isRegion : Job m ports → Prop
  | .region .. => True
  | _ => False

private theorem positive_depth (reached : Prefix m job next pending) (region : isRegion job) :
    0 < pending.depth := by
  induction reached with
  | apply => cases region
  | later first more ih => exact ih trivial
  | inside => exact Nat.succ_pos _
  | gamma => cases region
  | theta => cases region
  | iteration => cases region

theorem entry_grows {entry : Entry m} {pending : Pending m next.results entry.results}
    (reached : Prefix m entry.openBody next pending) (stack : Stack m entry.results final) :
    stackDepth stack < stackDepth (pending.push stack) := by
  rw [depth_push]
  exact Nat.lt_add_of_pos_right (positive_depth reached trivial)

theorem stack_grows (run : Run m) (base : Stack m (run.entry 0).results final) (n : Nat) :
    stackDepth (run.stackAt base n) < stackDepth (run.stackAt base (n + 1)) :=
  entry_grows (run.reaches n) (run.stackAt base n)

private theorem infinite_of_segments (boundary : Nat → State m final)
    (segments : ∀ n, TransGen Step (boundary n) (boundary (n + 1))) :
    InfiniteTrace Step (boundary 0) := by
  apply InfiniteTrace.coinduct (fun state => ∃ i, TransGen Step state (boundary i)) ?_
    ⟨1, segments 0⟩
  rintro state ⟨i, path⟩
  obtain ⟨next, edge, later⟩ := TransGen.head'_iff.mp path
  refine ⟨next, edge, ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp later with same | remaining
  · subst next
    exact ⟨i + 1, segments i⟩
  · exact ⟨i, remaining⟩

private theorem position_of_path {micro : Nat → State m final} {i : Nat} {target : State m final}
    (steps : ∀ j, Step (micro j) (micro (j + 1))) (path : ReflTransGen Step (micro i) target) :
    ∃ count : Nat, micro (i + count) = target := by
  induction path with
  | refl => exact ⟨0, rfl⟩
  | tail path edge ih =>
    obtain ⟨count, reached⟩ := ih
    refine ⟨count + 1, ?_⟩
    rw [Nat.add_succ]
    exact step_deterministic (steps (i + count)) (reached.symm ▸ edge)

private theorem next_position {micro : Nat → State m final} {i : Nat} {target : State m final}
    (steps : ∀ j, Step (micro j) (micro (j + 1))) (path : TransGen Step (micro i) target) :
    ∃ j, i < j ∧ micro j = target := by
  obtain ⟨before, more, edge⟩ := TransGen.tail'_iff.mp path
  obtain ⟨count, reached⟩ := position_of_path steps more
  exact ⟨i + count + 1, by omega, step_deterministic (steps (i + count)) (reached.symm ▸ edge)⟩

theorem checkpoints (run : Run m) (base : Stack m (run.entry 0).results final) :
    ∃ micro positions, Checkpoints run base micro positions := by
  classical
  let boundary (n : Nat) := (run.entry n).state (run.stackAt base n)
  have segments (n : Nat) : TransGen Step (boundary n) (boundary (n + 1)) :=
    entry_steps (run.reaches n) (run.stackAt base n)
  obtain ⟨micro, initial, steps⟩ := infinite_of_segments boundary segments
  let extend (n : Nat) (i : {i // micro i = boundary n}) : {j // i.val < j ∧ micro j = boundary (n + 1)} :=
    Classical.indefiniteDescription _ (next_position steps (i.property.symm ▸ segments n))
  let index : (n : Nat) → {i // micro i = boundary n} :=
    Nat.rec ⟨0, initial⟩ fun n i => ⟨(extend n i).val, (extend n i).property.2⟩
  exact ⟨micro, fun n => (index n).val, rfl, steps,
    fun n => (extend n (index n)).property.1, fun n => (index n).property⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Proofs
