module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Thms

/-! # Denotation on the two canonical return quotients -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

include shared in
/-- The two case/unary generators have a common graph denotation at both typings. -/
theorem stepDenotes : Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ) pe) J M := by
  intro Γ r s L e hr hs
  exact ⟨_, denoteRegion_spec J M hr,
    (eqv_sound pe J M shared (.extra hr hs e) hr hs).symm ▸ denoteRegion_spec J M hs⟩

/-- Interpret the quotient by unary fusion and pure case-return splitting. -/
noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C :=
  Extension.Singleton.denoteFunctor J M shared (by exact stepDenotes pe J M shared)

/-- The quotient lift computes the ordinary denotation of any guarded representative. -/
theorem denoteFunctor_map_ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    (denoteFunctor pe J M shared).map (Extension.Singleton.ofRegion (Step pe) hr) =
      denoteSingletonRegion J M hr.hasType :=
  Extension.Singleton.denoteFunctor_map_ofRegion J M shared (stepDenotes pe J M shared) hr

/-- Interpret the larger quotient that also includes projection returns and unit η. -/
noncomputable def joinedDenoteFunctor : Extension.Singleton.TypeCategory (JoinedStep (τ := τ) (Φ := Φ) pe) ⥤ C :=
  Extension.Singleton.denoteFunctor J M shared (by
    intro Γ r s L e hr hs
    exact ⟨_, denoteRegion_spec J M hr,
      (joined_eqv_sound pe J M shared (.extra hr hs e) hr hs).symm ▸ denoteRegion_spec J M hs⟩)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseAndUnaryReturns
