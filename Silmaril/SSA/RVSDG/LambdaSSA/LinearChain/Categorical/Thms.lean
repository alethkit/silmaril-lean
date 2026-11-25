module

public import Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.LinearChain.Categorical.Fold

/-! # Preservation in the shared categorical LambdaSSA semantics -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
  (RegionDenotes RegionTypingCoherent denoteRegion)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
variable {A B E D : τ} {tail : List τ}

/-- The implicit-effect γ/θ arrow is a structural denotation of the actual typed CFG. -/
theorem region_denotes (s : Blocks Φ A B E D tail) :
    RegionDenotes J M (regionTyping s) (denote J M s) :=
  Proofs.region_denotes J M s

/-- Every translation witness identifies the implicit-effect γ/θ arrow with
the chosen categorical region arrow in a coherent LambdaSSA model. -/
theorem denoteRegion_eq [RegionTypingCoherent (Φ := Φ) J M]
    {r : Isotope.LambdaSSA.Region Φ} {g : Loop Φ A E D}
    (rel : Related A B E D tail r g) :
    denoteRegion J M rel.typing = denote J M rel.instructions :=
  (show RegionDenotes J M rel.typing (denote J M rel.instructions) from
    by cases rel with | loop s => exact region_denotes J M s).eq_denote.symm

/-- Reading the admitted RVSDG directly agrees with the categorical denotation of
the actual region supplied by its reverse translation fibre. -/
theorem raised_denoteRegion_eq [RegionTypingCoherent (Φ := Φ) J M]
    {g : Loop Φ A E D} (form : RVForm A B E D tail g) :
    denoteRegion J M (raise form).2.typing = denoteForm J M form := by
  cases form with
  | loop s => exact (region_denotes J M s).eq_denote.symm

end Silmaril.SSA.RVSDG.LambdaSSA.LinearChain.Categorical
