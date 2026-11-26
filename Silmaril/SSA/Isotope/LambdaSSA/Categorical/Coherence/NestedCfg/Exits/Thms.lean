module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.NestedCfg.Exits.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgExits

/-! # Outward payload maps for actual nested CFG witnesses -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- Invert both exact row witnesses and compare their computations at the
prescribed branch injections. -/
theorem RegionConstructorRoutes.denotes {Γ : VCtx (Ty κ)} {L K : LCtx (Ty κ)} {Y : V}
    {left : labelObj M L ⟶ Y} {right : labelObj M K ⟶ Y} {r s : Region Φ}
    (pair : RegionConstructorRoutes M left right Γ r s) :
    RegionDenotes.Routes M left right J Γ r s :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgExits.routes J M pair

/-- Actual inner cfg witnesses at one internal family commute with a
pure outward map if their original entries and internal rows do. Local
feedback is unchanged. The result uses the existing outward naturality
of the contextual iterate. -/
theorem CfgDenotesAt.postmap_of_routes {Γ : VCtx (Ty κ)} {L K : LCtx (Ty κ)} {n : Nat} (R : Fin (n + 1) → Ty κ)
    (out : labelObj M L ⟶ labelObj M K)
    {entry entry' : Region Φ} {blocks blocks' : Fin (n + 1) → Region Φ}
    (entryRoutes : RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn R) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn R) K) J Γ entry entry')
    (rowRoutes : ∀ i, RegionDenotes.Routes M
      (labelAppendSplit M (List.ofFn R) L ≫ coprod.map out (𝟙 _))
      (labelAppendSplit M (List.ofFn R) K) J (R i :: Γ) (blocks i) (blocks' i))
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    {g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M K)}
    (small : CfgDenotesAt J M R entry blocks f) (wide : CfgDenotesAt J M R entry' blocks' g) :
    g = f ≫ J.map out :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.NestedCfgExits.dispatch J M R out
    entryRoutes rowRoutes small wide

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
