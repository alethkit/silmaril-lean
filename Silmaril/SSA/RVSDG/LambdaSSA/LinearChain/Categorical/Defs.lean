module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Wires.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # The implicit-effect interpretation of the linear γ/θ lowering -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (splitMapCoprod)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B D X Y : τ} {tail : List τ}

/-- An instruction is a computation arrow. Its type equalities only transport the ports. -/
def call (p : TwoBlock.Instruction Φ X Y) : J.obj (M.obj X) ⟶ J.obj (M.obj Y) :=
  J.map (eqToHom (congrArg M.obj p.input.symm)) ≫ InstructionModel.denote p.op ≫
    J.map (eqToHom (congrArg M.obj p.output))

/-- Expose the choice and its dependent payload in the computation coproduct. -/
noncomputable def choice (p : TwoBlock.Instruction Φ X (Silmaril.coprod Y D)) :
    J.obj (M.obj X) ⟶ J.obj (M.obj Y) ⨿ J.obj (M.obj D) :=
  call J M p ≫ J.map (M.coprodIso Y D).hom ≫ splitMapCoprod J (M.obj Y) (M.obj D)

/-- The selected body arm runs each primitive before passing its value to the next one. -/
noncomputable def bodyFold :
    {B : τ} → {tail : List τ} → Body Φ A D B tail →
      (J.obj (M.obj B) ⟶ J.obj (M.obj D) ⨿ J.obj (M.obj A))
  | _, _, .last p => choice J M p
  | _, _, .next p rest => call J M p ≫ bodyFold rest

/-- One θ activation. The header's left payload leaves at label 0. The right
payload enters the body arm, whose last instruction returns label 1 or feedback. -/
noncomputable def activation {E : τ} (s : Blocks Φ A B E D tail) :
    J.obj (M.obj A) ⟶ J.obj (labelObj M [E, D]) ⨿ J.obj (M.obj A) :=
  choice J M s.header ≫ coprod.desc
    (J.map (labelInject M (L := [E,D]) 0 rfl) ≫ coprod.inl)
    (bodyFold J M s.body ≫ coprod.map (J.map (labelInject M (L := [E,D]) 1 rfl)) (𝟙 _))

/-- The payload is the only loop variable in the value category. Effects are
implicit in the computation arrows and their iteration. -/
noncomputable def denote [Iteration C] {E : τ} (s : Blocks Φ A B E D tail) :
    J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E, D]) :=
  J.map (CartesianMonoidalCategory.snd (𝟙_ V) (M.obj A)) ≫ iterate (activation J M s)

/-- Interpret the admitted RVSDG shape from its syntactic witness. -/
noncomputable def denoteForm [Iteration C] {E : τ} {g : Loop Φ A E D} :
    RVForm A B E D tail g → (J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E, D]))
  | .loop s => denote J M s

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
