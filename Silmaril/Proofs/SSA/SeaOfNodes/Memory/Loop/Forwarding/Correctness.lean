module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Proofs

open RVSDG (Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Memory.Forwarding.Candidate}
variable {certificate : Memory.Forwarding.Disjoint.Certificate args} {input : Tuple (Val cells) args}

private theorem rewrite_result (success : rewrite graph candidate certificate input = some rewritten) :
    Memory.Forwarding.Disjoint.rewrite graph.body candidate certificate input = some rewritten.body ∧
      rewritten.stop = graph.stop := by
  cases bodyResult : Memory.Forwarding.Disjoint.rewrite graph.body candidate certificate input with
  | none => simp [rewrite, bodyResult] at success
  | some body =>
    by_cases admitted : accesses body = (true, true)
    · have result : Graph.mk body admitted graph.stop = rewritten := by
        simpa [rewrite, bodyResult, admitted] using success
      subst rewritten
      exact ⟨rfl, rfl⟩
    · simp [rewrite, bodyResult, admitted] at success

theorem rewrite_body_denote (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) : rewritten.body.denote input heap = graph.body.denote input heap :=
  Memory.Forwarding.Disjoint.rewrite_denote input heap (rewrite_result success).1

theorem rewrite_step (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) : rewritten.step input heap = graph.step input heap := by
  have stop : rewritten.stopWord input = graph.stopWord input :=
    congrArg input.get (rewrite_result success).2
  simp only [Graph.step, rewrite_body_denote success heap, stop]

theorem rewrite_evalAfter (success : rewrite graph candidate certificate input = some rewritten)
    (heap : Heap cells) (count : Nat) :
    rewritten.evalAfter input heap count = graph.evalAfter input heap count := by
  unfold Graph.evalAfter
  induction count generalizing heap with
  | zero => simp only [Graph.evalFrom, rewrite_step success heap]
  | succ count ih =>
    simp only [Graph.evalFrom, rewrite_step success heap]
    cases graph.step input heap with
    | inl => rfl
    | inr next => exact ih next

theorem rewrite_denote (success : rewrite graph candidate certificate input = some rewritten)
    (initial : Heap cells) : rewritten.denote input initial = graph.denote input initial := by
  unfold Graph.denote
  exact congrArg (fun step => Silmaril.Elgot.Part.run step initial)
    (funext fun heap => congrArg Part.some (rewrite_step success heap))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Proofs
