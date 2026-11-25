module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Singleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind

/-! # The categorical binary-let consumer for the opt-in singleton quotient -/

public section

universe u v w u₁ v₁

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (ModelComparisons)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet
  (applyPackedPair_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (diagonal_typed returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}

/-- Equality of singleton representatives is exactly the binary-let
extension relation at the same typed interface. -/
theorem ofRegion_eq_iff {r s : Region Φ}
    (hr : ValueBranches [A] r [B]) (hs : ValueBranches [A] s [B]) :
    ofRegion (τ := τ) hr = ofRegion (τ := τ) hs ↔ WithBinaryLetBind.Eqv [A] r s [B] :=
  Paper.Extension.Singleton.ofRegion_eq_iff BinaryLetBind.Step hr hs

/-- Literal binary let agrees with ordinary categorical composition of the
diagonal, retained scrutinee evaluation, and the packed body. -/
theorem assemble_let₂ (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D]) :
    (ofRegion (τ := τ) (diagonal_typed (Φ := Φ) X) ≫
      (whiskerLeftFunctor (ofType (Φ := Φ) X)).map (ofRegion (τ := τ) (returnOnce_typed ha))) ≫
        ofRegion (τ := τ) hp =
      ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind.assemble_let₂ ha hp

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

/-- Project the interpreted singleton arrow to the opt-in category. The body
comparison takes place in that quotient. -/
theorem compare_let₂ (cmp : ModelComparisons J M objIso pe)
    (ha : Tm.HasType [X] a (product A B))
    (hp : ValueBranches [product X (product A B)] p [D])
    (hBody : (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso (denoteSingletonRegion J M hp.hasType)) = ofRegion (τ := τ) hp) :
    (projection (τ := τ) (Φ := Φ)).map (reindexHom J M objIso
      (denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType))) =
        ofRegion (τ := τ) (.let₂ ha (applyPackedPair_typed hp)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBinaryLetBind.compare_let₂ J M objIso pe cmp ha hp hBody

end Denotation

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton
