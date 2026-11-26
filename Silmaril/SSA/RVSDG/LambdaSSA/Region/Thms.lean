module

public import Silmaril.SSA.RVSDG.LambdaSSA.Region.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Region.Agreement

/-! # Single-exit region fibres and categorical agreement -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Region Tm)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical (ctxObj labelObj labelInject Denotes RegionDenotes)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v d h c k
variable {Φ : Type v} {r : Region Φ} {t : Tm Φ}

theorem exitExpression_eq_some : exitExpression r = some t ↔ ExitExpression r t :=
  Proofs.exit_expression_iff

theorem exitRegion_related (t : Tm Φ) : ExitExpression (exitRegion t) t :=
  Proofs.exit_region t

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {Γ : List τ} {A : τ} {sigs : List (Ports (Ty τ))} {extra : Nat}

theorem ExitExpression.typing (h : ExitExpression r t) (ht : Tm.HasType Γ t A) :
    Region.HasType Γ r [A] :=
  Proofs.exit_typing h ht

theorem RegionRelated.typing {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]}
    (h : RegionRelated r g) : Region.HasType Γ r [A] :=
  h.represents.typing h.graph.typing

theorem GammaRegionRelated.typing {g : GammaGraph Φ extra Γ A} (h : GammaRegionRelated r g) :
    Region.HasType (selectorType (extra + 1) :: Γ) r [A] :=
  h.represents.typing h.graph.typing

/-- Recover a canonical single-exit λSSA region from the graph fibre. -/
@[expose] def raiseRegion (g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]) (h : GraphForm g) :
    Σ r : Region Φ, RegionRelated r g :=
  let ⟨t, rel⟩ := raiseGraph g h
  ⟨exitRegion t, ⟨t, exitRegion_related t, rel⟩⟩

/-- Recover a region-level case spine where each arm jumps to exit zero. -/
@[expose] def raiseGammaRegion (g : GammaGraph Φ extra Γ A) (h : GammaRVForm extra g.toTerm) :
    Σ r : Region Φ, GammaRegionRelated r g :=
  let ⟨t, rel⟩ := raiseGammaGraph g h
  ⟨exitRegion t, ⟨t, exitRegion_related t, rel⟩⟩

variable {D : Type d} {C : Type c} [Category.{h} D] [CartesianMonoidalCategory D]
  [HasFiniteCoproducts D] [SymmetricCategory D] [DistributiveTensor D]
  [Category.{k} C] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : D ⥤ C) [StrongElgotFreydCategory J] (M : TypeModel τ D) [InstructionModel J M Φ]

/-- A region denotation routes the expression's result to its unique exit.
The proof preserves the actual region binding and contextual case rules. -/
theorem ExitExpression.denotes (rel : ExitExpression r t) {ht : Tm.HasType Γ t A}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)} (d : Denotes J M ht f) :
    RegionDenotes J M (rel.typing ht) (f ≫ J.map (labelInject M (L := [A]) 0 rfl)) :=
  Proofs.exit_denotes J M rel d

variable (sel : Categorical.Selectors D) (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))

/-- Every straight-line relation witness preserves the singleton exit observation. -/
theorem RegionRelated.sound
    (agree : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))
    {g : Graph (Opcode Φ) (inputs Γ) [] sigs [.value A]} (rel : RegionRelated r g) :
    ∃ f, RegionDenotes J M rel.typing f ∧
      J.map (entryMap M Γ sel prim) ≫ f =
        J.map (g.denote (valueModel M sel prim) ≫
          (ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl) :=
  Proofs.region_sound J M sel prim agree rel

/-- Every terminal-switch relation witness preserves the singleton exit observation. -/
theorem GammaRegionRelated.sound
    {g : GammaGraph Φ extra Γ A} (rel : GammaRegionRelated r g) :
    ∃ f, RegionDenotes J M rel.typing f ∧
      J.map (gammaEntryMap M sel prim extra Γ) ≫ f =
        J.map (g.denote (valueModel M sel prim) ≫
          (ρ_ (M.obj A)).hom ≫ labelInject M (L := [A]) 0 rfl) :=
  Proofs.gamma_region_sound J M sel prim rel

end Silmaril.SSA.RVSDG.LambdaSSA
