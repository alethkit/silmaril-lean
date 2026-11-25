module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms

/-! # Loop-free singleton reification premises -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification

open Silmaril
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody (applyPacked_typed)

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (retainLeft)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedLet (returnOnce_typed)
open Silmaril.Isotope.LambdaSSA.Region.Paper.RetainedCase (reindexHom returnSum_typed)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory.ConstructorReification (unitMap fstMap sndMap inlMap inrMap)

universe u v w u₃ v₃
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₃} [Category.{v₃} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "C" => Paper.TypeCategory (τ := τ) Φ

variable
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ T : τ, J.obj (M.obj T) ≅ ofType (Φ := Φ) T)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- A loop-free singleton representative built by exposing each retained
body on a packed record. Scrutinee terms retain their original typing.
A binary-let node carries the comparison between its two guarded return forms. -/
inductive LoopFree : {X D : τ} → {r : Region Φ} → ValueBranches [X] r [D] → Prop where
  | branch {X D : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a D) :
      LoopFree (.br (ℓ := 0) rfl ha)
  | let₁ {X A D : τ} {a : Tm Φ} {p : Region Φ}
      (ha : Tm.HasType [X] a A) {hp : ValueBranches [Silmaril.product X A] p [D]}
      (body : LoopFree hp) : LoopFree (.let₁ ha (applyPacked_typed hp))
  | let₂ {X A B D : τ} {a : Tm Φ} {p : Region Φ}
      (ha : Tm.HasType [X] a (Silmaril.product A B))
      {hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]}
      (producer : Paper.Eqv [X] (BinaryLet.returnPair a) (Paper.RetainedLet.returnOnce a)
        [Silmaril.product A B])
      (body : LoopFree hp) : LoopFree (.let₂ ha (BinaryLet.applyPackedPair_typed hp))
  | case {X A B D : τ} {a : Tm Φ} {p q : Region Φ}
      (ha : Tm.HasType [X] a (Silmaril.coprod A B))
      {hp : ValueBranches [Silmaril.product X A] p [D]}
      {hq : ValueBranches [Silmaril.product X B] q [D]}
      (left : LoopFree hp) (right : LoopFree hq) :
      LoopFree (.case ha (applyPacked_typed hp) (applyPacked_typed hq))
  | cfgZero {X D : τ} {p : Region Φ} {hp : ValueBranches [X] p [D]}
      (entry : LoopFree hp) (blocks : Fin 0 → Region Φ) :
      LoopFree (.cfg Fin.elim0 hp (fun i => i.elim0) :
        ValueBranches [X] (.cfg p 0 blocks) [D])

/-- The primitive comparison premises for loop-free singleton reification.
Product extensionality is used only between pure-return arrows. -/
structure ModelComparisons : Prop where
  unit (X : τ) : reindexHom J M objIso (J.map (unitMap M X)) =
    ofRegion (τ := τ) (.br (ℓ := 0) (A := Silmaril.unit) rfl (.unit (Γ := [X])))
  fst (A B : τ) : reindexHom J M objIso (J.map (fstMap M A B)) =
    ofRegion (τ := τ) (productFstBranches A B)
  snd (A B : τ) : reindexHom J M objIso (J.map (sndMap M A B)) =
    ofRegion (τ := τ) (productSndBranches A B)
  inl (A B : τ) : reindexHom J M objIso (J.map (inlMap M A B)) = (sumCofan (Φ := Φ) A B).inl
  inr (A B : τ) : reindexHom J M objIso (J.map (inrMap M A B)) = (sumCofan (Φ := Φ) A B).inr
  imagePure {X A : τ} (f : M.obj X ⟶ M.obj A) : PureReturn pe (reindexHom J M objIso (J.map f))
  projectionExtensionality {X A B : τ} {f g : ofType (Φ := Φ) X ⟶ ofType (Silmaril.product A B)} :
    PureReturn pe f → PureReturn pe g →
    f ≫ ofRegion (τ := τ) (productFstBranches A B) = g ≫ ofRegion (τ := τ) (productFstBranches A B) →
    f ≫ ofRegion (τ := τ) (productSndBranches A B) = g ≫ ofRegion (τ := τ) (productSndBranches A B) →
    f = g
  whisker {Y A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)) :
    reindexHom J M objIso (J.map (M.productIso Y A).hom ≫ retainLeft J (R := M.obj Y) f ≫
      J.map (M.productIso Y B).inv) = whiskerLeft (ofType (Φ := Φ) Y) (reindexHom J M objIso f)
  producer {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) :
    reindexHom J M objIso (denoteSingletonRegion J M (returnOnce_typed ha).hasType) =
      ofRegion (τ := τ) (returnOnce_typed ha)
  sumProducer {X A B : τ} {a : Tm Φ} (ha : Tm.HasType [X] a (Silmaril.coprod A B)) :
    reindexHom J M objIso (denoteSingletonRegion J M (returnSum_typed ha).hasType) =
      ofRegion (τ := τ) (returnSum_typed ha)

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification
