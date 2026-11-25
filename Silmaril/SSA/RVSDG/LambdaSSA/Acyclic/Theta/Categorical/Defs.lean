module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Lowering.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Defs

/-! # Premonoidal semantics of the acyclic body inside θ -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd)
open Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LinearChain.Categorical (choice)
open Acyclic.Categorical (denoteForm)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B K E D : τ}

/-- The join's left payload exits at label 1. Its right payload is the
new θ parameter. The header can return directly at label 0. -/
noncomputable def activation (s : Loop Φ A B K E D) :
    J.obj (M.obj A) ⟶ J.obj (labelObj M [E,D]) ⨿ J.obj (M.obj A) :=
  choice J M s.header ≫ coprod.desc
    (J.map (labelInject M (L := [E,D]) 0 rfl) ≫ coprod.inl)
    (denoteForm J M (.body s.body) ≫ choice J M s.join ≫
      coprod.map (J.map (labelInject M (L := [E,D]) 1 rfl)) (𝟙 _))

noncomputable def denote [Iteration C] (s : Loop Φ A B K E D) :
    J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E,D]) :=
  J.map (snd (ctxObj M []) (M.obj A)) ≫ iterate (activation J M s)

/-- The admitted θ packs label exits at the syntax boundary. Its semantic
iteration state is just the header payload. -/
noncomputable def denoteLoop [Iteration C] {term : Term Φ A E D} :
    Form A B K E D term → (J.obj (ctxObj M [A]) ⟶ J.obj (labelObj M [E,D]))
  | .loop s => denote J M s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical
