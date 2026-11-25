module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Soundness

/-! # Preservation of one-block tail-controlled loops -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} {C : Type c} [Category.{h} D] [Category.{k} C]
  [CartesianMonoidalCategory D] [SymmetricCategory D] [HasFiniteCoproducts D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor D] [DistributivePremonoidalCategory C] [Iteration C]
  [ElgotCategory C]
variable (J : D ⥤ C) [StrongElgotFreydCategory J]
variable (M : TypeModel τ D) [InstructionModel J M Φ]
variable (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
variable (agrees : ∀ f, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))

include agrees

/-- For every translation witness, the adapted θ arrow satisfies the repository's
structural denotation judgment for the typed ΛSSA region. -/
theorem Related.preserves (sel : Categorical.Selectors D)
    {A : τ} {r : Region Φ} {g : LoopGraph Φ A} (rel : Related A r g) :
    RegionDenotes J M rel.typing
      (J.map (entryMap M A) ≫ g.denote J (valueModel M prim sel) ≫
        J.map ((ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl)) :=
  Proofs.preserves J M prim agrees sel rel

/-- In coherent region models the comparison is an equality with the chosen
ΛSSA denotation. The structural judgment above uses no coherence assumption. -/
theorem Related.denoteRegion_eq [RegionTypingCoherent (Φ := Φ) J M]
    (sel : Categorical.Selectors D) {A : τ} {r : Region Φ} {g : LoopGraph Φ A}
    (rel : Related A r g) :
    denoteRegion J M rel.typing =
      J.map (entryMap M A) ≫ g.denote J (valueModel M prim sel) ≫
        J.map ((ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl) :=
  (rel.preserves J M prim agrees sel).eq_denote.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Theta
