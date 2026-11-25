module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Graph
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Region

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} {C : Type c} [Category.{h} D] [Category.{k} C]
  [CartesianMonoidalCategory D] [SymmetricCategory D] [HasFiniteCoproducts D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor D] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
variable (J : D ⥤ C) [StrongElgotFreydCategory J]
variable (M : TypeModel τ D) [InstructionModel J M Φ]
variable (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
variable (agrees : ∀ f, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))

include agrees

theorem preserves (sel : Categorical.Selectors D)
    {A : τ} {r : Region Φ} {g : LoopGraph Φ A} (rel : Related A r g) :
    RegionDenotes J M rel.typing
      (J.map (entryMap M A) ≫ g.denote J (valueModel M prim sel) ≫
        J.map ((ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl)) := by
  cases rel with
  | loop s =>
    let p := (ρ_ (M.obj A)).hom
    let i := labelInject M (L := [A]) 0 rfl
    let loop : J.obj (M.obj A ⊗ 𝟙_ D) ⟶ J.obj (M.obj A ⊗ 𝟙_ D) :=
      (graph s).denote J (valueModel M prim sel)
    have project : loop ≫ J.map p = J.map p ≫
        iterate (J.map (stepMap M prim s) ≫
          Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.splitMapCoprod J
            (M.obj A) (M.obj A)) :=
      graph_projects J M prim sel s
    change RegionDenotes J M (regionTyping s) (J.map (entryMap M A) ≫ loop ≫ J.map (p ≫ i))
    rw [J.map_comp p i, ← Category.assoc loop, project]
    have entry :
        J.map (entryMap M A) ≫ J.map p =
          J.map (CartesianMonoidalCategory.snd (𝟙_ D) (M.obj A)) := by
      rw [← J.map_comp (entryMap M A) p]
      apply congrArg (fun f => J.map f)
      change ((λ_ (M.obj A)).hom ≫ (ρ_ (M.obj A)).inv) ≫ (ρ_ (M.obj A)).hom =
        CartesianMonoidalCategory.snd (𝟙_ D) (M.obj A)
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        CartesianMonoidalCategory.leftUnitor_hom]
    simp only [Category.assoc]
    rw [← Category.assoc (J.map (entryMap M A)) (J.map p), entry]
    exact region_iterates M J prim agrees s

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs
