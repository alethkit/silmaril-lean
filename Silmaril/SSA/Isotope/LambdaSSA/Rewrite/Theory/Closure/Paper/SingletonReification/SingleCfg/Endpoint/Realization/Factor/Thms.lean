module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Factor.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural

/-! # Exact comparison of structural carried-step factors -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (whiskerLeftRegion)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (ofType ofRegion sumIso whiskerLeft)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification (ModelComparisons)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v u₁ v₁ w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X S D : τ}

/-- The capture duplication prefix preserves the original state as the right factor. -/
theorem duplicateCapture_typed (X S : τ) :
    ValueBranches [product X S] (duplicateCapture : Region Φ) [product X (product X S)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.duplicateCapture_typed
    X S

/-- The suffix routes each live label to the appropriate carried payload. -/
theorem retagPacked_typed (X S D : τ) :
    ValueBranches [product X (packedExitType [S, D])] (retagPacked (Φ := Φ) S D)
      [coprod (product X D) (product X S)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.retagPacked_typed
    X S D

/-- The carried step duplicates the capture, runs the original block once
under left whiskering, and retags the exits. -/
theorem realizePackedStep_factor {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    Paper.Eqv [product X S]
      (compLSubst (compLSubst (fun _ => duplicateCapture) (fun _ => whiskerLeftRegion b))
        (fun _ => retagPacked S D) 0)
      (realizePackedStep S D b) [coprod (product X D) (product X S)] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.realizePackedStep_factor
    hb

/-- The same factorization holds in the syntactic singleton quotient. -/
theorem realizePackedStep_arrow {b : Region Φ}
    (hb : ValueBranches [product X S] b [packedExitType [S, D]]) :
    (ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S) ≫ whiskerLeft (ofType X) (ofRegion (τ := τ) hb)) ≫
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) = ofRegion (τ := τ) (realizePackedStep_typed hb) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.realizePackedStep_arrow
    hb

/-- An equality of exact-sum step arrows transports through the local entry continuation. -/
theorem canonicalExitContinuation_congr {s t : Region Φ}
    (hs : ValueBranches [product X S] s [coprod (product X D) (product X S)])
    (ht : ValueBranches [product X S] t [coprod (product X D) (product X S)])
    (h : ofRegion (τ := τ) hs = ofRegion (τ := τ) ht) :
    Paper.Eqv [packedExitType [S, D], X] (canonicalExitContinuation X S s)
      (canonicalExitContinuation X S t) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.canonicalExitContinuation_congr
    hs ht h

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

variable [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- Agreement of the two structural factors identifies the model-selected arrow with the explicit carried step. -/
theorem carriedStep_eq_realizePackedStep {b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (prefixEq : capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S))
    (routeEq : carriedRoute J M objIso X S D =
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫ (sumIso (product X D) (product X S)).hom) :
    carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
      ofRegion (τ := τ) (realizePackedStep_typed hb) ≫ (sumIso (product X D) (product X S)).hom :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.carriedStep_eq_realizePackedStep
    J M objIso cmp hb prefixEq routeEq

/-- Agreement of the structural factors gives the original local continuation
for a representative chosen by one-block model reification. -/
theorem canonicalExitContinuation_eq_of_carriedStep {b step : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (hb : ValueBranches [product X S] b [packedExitType [S, D]])
    (hs : ValueBranches [product X S] step [coprod (product X D) (product X S)])
    (prefixEq : capturePrefix J M objIso X S = ofRegion (τ := τ) (duplicateCapture_typed (Φ := Φ) X S))
    (routeEq : carriedRoute J M objIso X S D =
      ofRegion (τ := τ) (retagPacked_typed (Φ := Φ) X S D) ≫ (sumIso (product X D) (product X S)).hom)
    (hStep : carriedStep J M objIso X S D ((objIso (product X S)).hom ≫
      ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
        ofRegion (τ := τ) hs ≫ (sumIso (product X D) (product X S)).hom) :
    Paper.Eqv [packedExitType [S, D], X] (canonicalExitContinuation X S step)
      (carriedExitContinuation X S D b) [D] :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingleCfgStructural.canonicalExitContinuation_eq_of_carriedStep
    J M objIso cmp hb hs prefixEq routeEq hStep

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
