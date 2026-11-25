module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs

/-! # Collapsing forward edges in a categorical linear dispatcher -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w h k

variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [ElgotFreydCategory J]

variable (M : TypeModel τ V) [InstructionModel J M Φ]
variable {A B D : τ} {tail : List τ} {I O : C}

/-- Forward edges recur inside the inner dispatcher. The final block returns
to the outer dispatcher with either an external payload or a header payload. -/
def routes (f : I ⟶ O ⨿ I) (finish : J.obj (M.obj D) ⨿ J.obj (M.obj A) ⟶ O) :
    {B : τ} → {tail : List τ} → Body Φ A D B tail →
    (∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ I) → Prop
  | _, _, .last p, locate => locate 0 ≫ f = choice J M p ≫ finish ≫ coprod.inl
  | _, _, .next p rest, locate =>
    (locate 0 ≫ f = call J M p ≫ locate (0 : Fin _).succ ≫ coprod.inr) ∧
      routes f finish rest (fun i => locate i.succ)

theorem iter_body (f : I ⟶ O ⨿ I) (finish : J.obj (M.obj D) ⨿ J.obj (M.obj A) ⟶ O)
    (body : Body Φ A D B tail)
    (locate : ∀ i : Fin (B :: tail).length, J.obj (M.obj ((B :: tail).get i)) ⟶ I)
    (steps : routes J M f finish body locate) :
    locate 0 ≫ iterate f = bodyFold J M body ≫ finish := by
  induction body with
  | last p =>
    change locate 0 ≫ f = choice J M p ≫ finish ≫ coprod.inl at steps
    rw [ElgotCategory.fixpoint f, ← Category.assoc, steps]
    simp [bodyFold]
  | @next B X xs p rest ih =>
    obtain ⟨step, more⟩ := steps
    rw [ElgotCategory.fixpoint f, ← Category.assoc, step]
    let next : J.obj (M.obj X) ⟶ I := locate (0 : Fin _).succ
    change (call J M p ≫ next ≫ coprod.inr) ≫ coprod.desc (𝟙 O) (iterate f) =
      (call J M p ≫ bodyFold J M rest) ≫ finish
    simp only [Category.assoc, coprod.inr_desc]
    exact congrArg (fun k => call J M p ≫ k) (ih (fun i => locate i.succ) more)

omit [InstructionModel J M Φ] in
/-- Codiagonal fuses the two rounds and pure uniformity restricts feedback to
the header injection. The step arrows may be arbitrary computations. -/
theorem close_grouped {H I : V} {Z : C} (enter : H ⟶ I)
    (inner : J.obj I ⟶ (Z ⨿ J.obj I) ⨿ J.obj I)
    (round : J.obj H ⟶ Z ⨿ J.obj H)
    (square : J.map enter ≫ iterate inner = round ≫ coprod.map (𝟙 Z) (J.map enter)) :
    J.map enter ≫ iterate (inner ≫ coprod.desc (𝟙 (Z ⨿ J.obj I)) coprod.inr) = iterate round := by
  rw [← ElgotCategory.codiagonal]
  exact (ElgotFreydCategory.pure_uniformity J round (iterate inner) enter square.symm).symm

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Proofs
