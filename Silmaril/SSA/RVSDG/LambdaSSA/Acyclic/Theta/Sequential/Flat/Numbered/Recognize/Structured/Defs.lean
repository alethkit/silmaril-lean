module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Defs

/-! # The sequence association chosen by the label parser -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- Each local region has a right-associated nonempty sequence of
instructions and binary choices. The arms are themselves in this form. -/
inductive RightAssociated : {A B : τ} → Body Φ A B → Prop where
  | instruction {A B : τ} (op : TwoBlock.Instruction Φ A B) :
      RightAssociated (.instruction op)
  | choice {A X Y B : τ} (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
      {left : Body Φ X B} {right : Body Φ Y B} :
      RightAssociated left → RightAssociated right → RightAssociated (.choice op left right)
  | thenInstruction {A X B : τ} (op : TwoBlock.Instruction Φ A X) {rest : Body Φ X B} :
      RightAssociated rest → RightAssociated (.sequence (.instruction op) rest)
  | thenChoice {A X Y K B : τ} (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
      {left : Body Φ X K} {right : Body Φ Y K} {rest : Body Φ K B} :
      RightAssociated left → RightAssociated right → RightAssociated rest →
        RightAssociated (.sequence (.choice op left right) rest)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize
