module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs

open TwoBlock.TwoExit (Carrier ExitCode)
open Wires.Reverse (Vertex)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A I B K M C J E D : τ}

private def atomLabels {X S T Y Z : τ}
    (header : TwoBlock.Instruction Φ X (Silmaril.coprod Y S))
    (op : TwoBlock.Instruction Φ S T)
    (join : TwoBlock.Instruction Φ T (Silmaril.coprod Z X)) : List (Vertex (τ := τ) (Φ := Φ)) :=
  [.theta [.header header, .gamma [[.headerExit], [.call op, .join join]]]]

omit [DecidableEq Φ] in
private theorem body_atom {S T : τ} (fuel : Nat) (op : TwoBlock.Instruction Φ S T) :
    body (fuel + 1) S [.call op] = some ⟨T, .instruction op⟩ := by
  simp [body]

omit [DecidableEq Φ] in
private theorem loop_atom {X S T Y Z : τ} (fuel : Nat)
    (header : TwoBlock.Instruction Φ X (Silmaril.coprod Y S))
    (op : TwoBlock.Instruction Φ S T)
    (endOp : TwoBlock.Instruction Φ T (Silmaril.coprod Z X)) :
    loop (fuel + 1) X Y Z (atomLabels header op endOp) =
      some ⟨S, T, ⟨header, .instruction op, endOp⟩⟩ := by
  simp [atomLabels, loop, body_atom]

omit [DecidableEq Φ] in
private theorem guarded_atom (fuel : Nat)
    (gate : TwoBlock.Instruction Φ A (Carrier I M M))
    (header : TwoBlock.Instruction Φ I (Silmaril.coprod M B))
    (op : TwoBlock.Instruction Φ B K)
    (endOp : TwoBlock.Instruction Φ K (Silmaril.coprod M I)) :
    guarded (fuel + 1) A I M
      [.classifier (X := ExitCode M M) (Y := I) gate, .gamma [[], atomLabels header op endOp]] =
      some ⟨B, K, ⟨gate, ⟨header, .instruction op, endOp⟩⟩⟩ := by
  simp [guarded, loop_atom]

set_option maxHeartbeats 1000000 in
theorem complete_atomic
    (gate : TwoBlock.Instruction Φ A (Carrier I M M))
    (firstHeader : TwoBlock.Instruction Φ I (Silmaril.coprod M B))
    (firstBody : TwoBlock.Instruction Φ B K)
    (firstJoin : TwoBlock.Instruction Φ K (Silmaril.coprod M I))
    (secondHeader : TwoBlock.Instruction Φ M (Silmaril.coprod E C))
    (secondBody : TwoBlock.Instruction Φ C J)
    (secondJoin : TwoBlock.Instruction Φ J (Silmaril.coprod D M)) :
    (recognize (compile ⟨gate, ⟨firstHeader, .instruction firstBody, firstJoin⟩⟩
      ⟨secondHeader, .instruction secondBody, secondJoin⟩)).isSome = true := by
  let components : Components Φ A I M E D :=
    ⟨B, K, C, J, ⟨gate, ⟨firstHeader, .instruction firstBody, firstJoin⟩⟩,
      ⟨secondHeader, .instruction secondBody, secondJoin⟩⟩
  have cutReads : cut components.graph = some
      ([.classifier (X := ExitCode M M) (Y := I) gate, .gamma [[], atomLabels firstHeader firstBody firstJoin]],
        atomLabels secondHeader secondBody secondJoin) := by
    simp only [cut, Components.graph, compile, join, NestedTheta.Term.toTerm_toGraph]
    rfl
  have bounded : budget components.graph.toTerm = 24 := by
    simp only [Components.graph, compile, join, NestedTheta.Term.toTerm_toGraph]
    rfl
  have parsed : candidate components.graph = some components := by
    simp only [candidate, cutReads, bounded]
    change (do
      let ⟨b, k, first⟩ ← guarded (23 + 1) A I M
        [.classifier (X := ExitCode M M) (Y := I) gate, .gamma [[], atomLabels firstHeader firstBody firstJoin]]
      let ⟨c, j, second⟩ ← loop (23 + 1) M E D (atomLabels secondHeader secondBody secondJoin)
      pure ⟨b, k, c, j, first, second⟩) = some components
    rw [guarded_atom, loop_atom]
    rfl
  change (recognize components.graph).isSome = true
  rw [complete components parsed rfl]
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Proofs
