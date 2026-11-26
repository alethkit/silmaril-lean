module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms

/-! # Completeness for two generated single-instruction loop bodies -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

open TwoBlock.TwoExit (Carrier)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ] [DecidableEq Φ]
variable {A I B K M C J E D : τ}

/-- Any generated graph in which each loop body is one typed instruction
is accepted. Both loops may take feedback. -/
theorem complete_atomic
    (gate : TwoBlock.Instruction Φ A (Carrier I M M))
    (firstHeader : TwoBlock.Instruction Φ I (Silmaril.coprod M B))
    (firstBody : TwoBlock.Instruction Φ B K)
    (firstJoin : TwoBlock.Instruction Φ K (Silmaril.coprod M I))
    (secondHeader : TwoBlock.Instruction Φ M (Silmaril.coprod E C))
    (secondBody : TwoBlock.Instruction Φ C J)
    (secondJoin : TwoBlock.Instruction Φ J (Silmaril.coprod D M)) :
    (recognize (compile ⟨gate, ⟨firstHeader, .instruction firstBody, firstJoin⟩⟩
      ⟨secondHeader, .instruction secondBody, secondJoin⟩)).isSome = true :=
  complete_generated _ _

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
