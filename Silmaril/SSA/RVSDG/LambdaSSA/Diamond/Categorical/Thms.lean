module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Fold

/-! # Preservation of the two-exit diamond loop -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical

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
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

variable {A B X Y K E D : τ}

/-- The γ/θ arrow is a structural denotation of the actual five-block CFG. -/
theorem region_denotes (s : Blocks Φ A B X Y K E D) :
    RegionDenotes J M (regionTyping s) (denoteForm J M (Form.loop s)) :=
  Proofs.region_denotes J M s

/-- Coherence identifies the actual CFG's chosen denotation with that of its
nested γ/θ lowering in the shared premonoidal model. -/
theorem denoteRegion_eq [RegionTypingCoherent (Φ := Φ) J M] (s : Blocks Φ A B X Y K E D) :
    denoteRegion J M (regionTyping s) = denoteForm J M (Form.loop s) :=
  (region_denotes J M s).eq_denote.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical
