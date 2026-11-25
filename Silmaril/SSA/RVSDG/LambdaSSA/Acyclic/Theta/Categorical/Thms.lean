module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Fold

/-! # A flat LambdaSSA loop denotes its structured θ lowering -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical (RegionDenotes RegionTypingCoherent denoteRegion)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [FreydCategory.CentralUnit J]

variable {A B K E D : τ}

/-- Group the generated acyclic part at the typed join, then iterate exactly
the header parameter of the admitted θ. -/
theorem region_denotes (s : Loop Φ A B K E D) :
    RegionDenotes J M (regionTyping s) (denoteLoop J M (.loop s)) :=
  Proofs.region_denotes J M s

theorem denoteRegion_eq [RegionTypingCoherent (Φ := Φ) J M] (s : Loop Φ A B K E D) :
    denoteRegion J M (regionTyping s) = denoteLoop J M (.loop s) :=
  (region_denotes J M s).eq_denote.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical
