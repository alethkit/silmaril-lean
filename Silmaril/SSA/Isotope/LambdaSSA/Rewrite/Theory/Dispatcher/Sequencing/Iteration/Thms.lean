module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LinkedIteration

/-! # Categorical fixpoint for linked iteration -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

variable {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]

theorem Region.HasType.linkedIterate {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p [Silmaril.coprod B A]) :
    Region.HasType (A :: Γ) (Region.linkedIterate A B p) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.linkedIterate_hasType hp

theorem Region.HasType.linkedFixpointRhs {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p [Silmaril.coprod B A]) :
    Region.HasType (A :: Γ) (Region.linkedFixpointRhs A B p) [B] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.linkedFixpointRhs_hasType hp

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- Linked iteration denotes the step followed by the linked return-or-repeat
continuation. The step can have arbitrary typed effects and nested CFGs. -/
theorem denoteRegion_linkedFixpoint {Γ : VCtx τ} {A B : τ} {p : Region Φ}
    (hp : Region.HasType (A :: Γ) p [Silmaril.coprod B A])
    (hi : Region.HasType (A :: Γ) (Region.linkedIterate A B p) [B])
    (hr : Region.HasType (A :: Γ) (Region.linkedFixpointRhs A B p) [B]) :
    denoteRegion J M hi = denoteRegion J M hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.denote_linked_fixpoint J M hp hi hr

end Semantics.Categorical
end Silmaril.Isotope.LambdaSSA
