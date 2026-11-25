module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification

/-! # Binary-let assembly and reification in the extended singleton category -/

public section

universe u v w u₁ v₁

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (ModelComparisons)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
  (returnPair_typed applyPackedPair_typed literal_let₂)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (diagonal_typed returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}

set_option backward.isDefEq.respectTransparency false in
theorem assemble_let₂ (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D]) :
    (ofRegion (τ := τ) (diagonal_typed (Φ := Φ) X) ≫
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).map (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        ofRegion (τ := τ) hp =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  have e : ofRegion (τ := τ) (returnOnce_typed ha) = ofRegion (τ := τ) (returnPair_typed ha) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step _ _).2
      (Paper.WithBinaryLetBind.returnPair_eq_returnOnce ha).symm
  rw [e]
  have ew := Paper.Extension.Singleton.whiskerLeft_map BinaryLetBind.Step
    (X := Paper.TypeCategory.ofType (Φ := Φ) X) (Paper.TypeCategory.ofRegion (τ := τ) (returnPair_typed ha))
  change ((projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) (diagonal_typed (Φ := Φ) X)) ≫
    (Paper.Extension.Singleton.whiskerLeftFunctor BinaryLetBind.Step
      (ofType (Φ := Φ) X)).map ((projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) (returnPair_typed ha)))) ≫
        (projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (τ := τ) hp) = _
  rw [ew, ← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((projection (τ := τ) (Φ := Φ)).map)
  rw [Paper.TypeCategory.whiskerLeft_ofRegion]
  let h := seqValueBranches (diagonal_typed (Φ := Φ) X) (whiskerLeftRegion_typed X (returnPair_typed ha))
  rw [Paper.TypeCategory.ofRegion_comp _ _ h,
    Paper.TypeCategory.ofRegion_comp h hp (seqValueBranches h hp)]
  exact (Paper.TypeCategory.ofRegion_eq_iff _ _).2 (literal_let₂ ha hp)

section Denotation

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ Paper.TypeCategory.ofType (Φ := Φ) T)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option backward.isDefEq.respectTransparency false in
theorem compare_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D])
    (hBody : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso (denoteSingletonRegion J M hp.hasType)) = ofRegion (τ := τ) hp) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType))) =
        ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) := by
  rw [SingletonReification.factor_let₂ J M objIso pe cmp ha hp, Functor.map_comp, Functor.map_comp, hBody]
  rw [← Paper.Extension.Singleton.whiskerLeft_map BinaryLetBind.Step]
  exact assemble_let₂ ha hp

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind
