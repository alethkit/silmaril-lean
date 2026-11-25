module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs

/-! # The implicit-effect interpretation of the nested diamond lowering -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain.Categorical (call choice)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B X Y K E D : τ}

/-- The classifier coproduct selects one arm. The common result is the join's
typed parameter. The two arms need not be central. -/
noncomputable def diamond (s : Branches Φ B X Y K) :
    J.obj (M.obj B) ⟶ J.obj (M.obj K) :=
  choice J M s.classifier ≫ coprod.desc (call J M s.left) (call J M s.right)

/-- The join executes after the selected arm. Its result chooses the second
external label or the next θ activation. -/
noncomputable def activation (s : Blocks Φ A B X Y K E D) :
    J.obj (M.obj A) ⟶ J.obj (labelObj M [E,D]) ⨿ J.obj (M.obj A) :=
  choice J M s.header ≫ coprod.desc
    (J.map (labelInject M (L := [E,D]) 0 rfl) ≫ coprod.inl)
    (diamond J M s.diamond ≫ choice J M s.join ≫
      coprod.map (J.map (labelInject M (L := [E,D]) 1 rfl)) (𝟙 _))

noncomputable def denote [Iteration C] (s : Blocks Φ A B X Y K E D) :
    J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E,D]) :=
  J.map (CartesianMonoidalCategory.snd (𝟙_ V) (M.obj A)) ≫ iterate (activation J M s)

/-- Interpret the real nested term on its admitted shape. At each γ the
matching selector and its typed payload are represented by one coproduct. -/
noncomputable def denoteForm [Iteration C] {g : Loop Φ A E D} :
    Form A B X Y K E D g → (J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E,D]))
  | .loop s => denote J M s

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical
