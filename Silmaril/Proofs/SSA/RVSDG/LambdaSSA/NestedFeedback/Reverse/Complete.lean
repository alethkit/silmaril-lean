module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Defs

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Proofs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ]
variable {A B K D : τ}

omit [TypeFormers τ] in
private theorem instructionAt_of {X Y : τ} (p : TwoBlock.Instruction Φ X Y) :
    instructionAt p.op X Y = some p := by
  obtain ⟨op, input, output⟩ := p
  simp [instructionAt, input, output]

theorem decode_generated (s : Loop Φ A B K D) :
    decode (.enter A B K D s.enter.op, .inner B K s.inner.op, .finish A B K D s.finish.op) =
      some ⟨B, K, s⟩ := by
  cases s
  simp [decode, instructionAt_of]

theorem candidate_generated (s : Loop Φ A B K D) :
    candidate (graph s) = some ⟨B, K, s⟩ := by
  rw [candidate, read, graph, NestedTheta.Term.toTerm_toGraph]
  exact decode_generated s

variable [DecidableEq Φ]

theorem recover_generated (s : Loop Φ A B K D) :
    recover (graph s) = some ⟨B, K, region s, .generated s⟩ := by
  rw [recover, recognize, candidate_generated]
  have accepted : certify (graph s) ⟨B, K, s⟩ = some ⟨⟨B, K, s⟩, rfl⟩ := by
    simp [certify]
  change Option.map Match.raise (certify (graph s) ⟨B, K, s⟩) = _
  rw [accepted]
  rfl

theorem recover_isSome_iff (g : Graph Φ A D) :
    (recover g).isSome = true ↔ ∃ (B K : τ) (s : Loop Φ A B K D), graph s = g := by
  constructor
  · intro accepted
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp accepted
    obtain ⟨b, k, r, relation⟩ := w
    cases relation with
    | generated s => exact ⟨b, k, s, rfl⟩
  · rintro ⟨b, k, s, rfl⟩
    rw [recover_generated]
    rfl

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Proofs
