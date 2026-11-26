module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Proofs

open RVSDG (Tuple)
open Memory.DeadStore (Candidate)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate} {facts : Certificate args}

private theorem rewrite_result (success : rewriteWith graph candidate facts = some rewritten) :
    Memory.DeadStore.rewriteWith graph.body candidate facts = some rewritten.body ∧
      rewritten.stop = graph.stop := by
  obtain ⟨body, checked, returned⟩ := Option.bind_eq_some_iff.mp success
  split at returned
  next =>
    cases Option.some.inj returned
    exact ⟨checked, rfl⟩
  next => cases returned

theorem rewrite_body_denote (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.body.denote input heap = graph.body.denote input heap :=
  Memory.DeadStore.rewriteWith_denote (rewrite_result success).1 input valid heap

theorem rewrite_step (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.step input heap = graph.step input heap := by
  have stop : rewritten.stopWord input = graph.stopWord input :=
    congrArg input.get (rewrite_result success).2
  simp only [Graph.step, rewrite_body_denote success input valid heap, stop]

theorem rewrite_evalAfter (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (initial : Heap cells) (count : Nat) :
    rewritten.evalAfter input initial count = graph.evalAfter input initial count := by
  unfold Graph.evalAfter
  induction count generalizing initial with
  | zero => simp only [Graph.evalFrom, rewrite_step success input valid initial]
  | succ count ih =>
    simp only [Graph.evalFrom, rewrite_step success input valid initial]
    cases graph.step input initial with
    | inl => rfl
    | inr next => exact ih next

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Proofs
