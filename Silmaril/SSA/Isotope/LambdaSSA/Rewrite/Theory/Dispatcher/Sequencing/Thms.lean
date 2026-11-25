module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Sequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LinkedCfgSequencing

/-! # Categorical sequencing through a linked CFG -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory.CartesianMonoidalCategory (snd)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

/-- A CFG can move through linked sequencing when the intermediate router
has a pure denotation that depends only on the incoming payload. The producer
and the recursive blocks may be arbitrary exactly typed regions. -/
theorem denoteRegion_linkedCfgSequencing {n : Nat} {Γ : VCtx τ} {P L : LCtx τ}
    {p : Region Φ} (R : Fin n → τ) {next : Nat → Region Φ} {blocks : Fin n → Region Φ}
    (hp : Region.HasType Γ p P)
    (hl : Region.HasType Γ (p.linkExits P next) (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (q : labelObj M P ⟶ labelObj M (List.ofFn R ++ L))
    (dn : ContinuationDenotes J M next (J.map (snd (ctxObj M Γ) (labelObj M P) ≫ q)))
    (hr : Region.HasType Γ (p.linkExits P (Region.cfgContinuations blocks next)) L) :
    denoteRegion J M (.cfg R hl hb) = denoteRegion J M hr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.linked_cfg_sequencing J M R hp hl hb q dn hr

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
