module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly

/-! # The local preservation premise for single-block reification -/

public section

universe u v u₁ v₁ w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open Paper.TypeCategory
open Paper.Extension.Singleton (projection)
open Paper.SingletonReification (ModelComparisons)
open Paper.RetainedCase (reindexHom)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel contextualStep)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop retainLeft)
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option hygiene false in
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Canonical Paper feedback commutes with the two carrier isomorphisms. -/
theorem canonical_reindex {U V X Y : Comp} (state : U ≅ X) (result : V ≅ Y)
    (step : U ⟶ V ⨿ U) :
    state.inv ≫ Paper.TypeCategory.iterate step ≫ result.hom =
      Paper.TypeCategory.iterate (reindexStep state result step) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.canonical_reindex
    state result step

/-- At the selected canonical operation, loop preservation holds by definition. -/
theorem canonicalIteration_preserves [HasFiniteCoproducts Comp] {U W : Comp} (step : U ⟶ W ⨿ U) :
    letI : Iteration Comp := canonicalIteration
    PreservesLoop step := rfl

/-- The exact-sum exit conversion has the guarded decoder as its representative. -/
theorem exitSum_ofRegion (S D : τ) :
    exitSumArrow (Φ := Φ) S D = ofRegion (τ := τ) (exitDecoder_typed S D) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.exitSum_ofRegion S D

/-- Following the head of the packed exit list reaches the repeat injection. -/
theorem exitDecoder_inl (S D : τ) :
    (sumCofan (Φ := Φ) S (coprod D Silmaril.empty)).inl ≫ ofRegion (τ := τ) (exitDecoder_typed S D) =
      (sumCofan D S).inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.exitDecoder_inl S D

/-- Following the second tag reaches the result injection. -/
theorem exitDecoder_inr_inl (S D : τ) :
    (sumCofan (Φ := Φ) D Silmaril.empty).inl ≫ (sumCofan S (coprod D Silmaril.empty)).inr ≫
      ofRegion (τ := τ) (exitDecoder_typed S D) = (sumCofan D S).inl :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.exitDecoder_inr_inl S D

/-- The canonical arrow is represented by the typed region with a carried loop. -/
theorem canonicalAssembly_ofRegion {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b
      [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]) :
    canonicalAssembly (ofRegion (τ := τ) he)
      (ofRegion (τ := τ) hb ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom) =
      ofRegion (τ := τ) (canonicalRegion_typed he hb) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.canonicalAssembly_ofRegion he hb

/-- Projected equality of the entry and the carried step survives canonical assembly. -/
theorem canonicalAssembly_map_congr
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {X S D : τ}
    {e e' : ofType (Φ := Φ) X ⟶ ofType (packedExitType [S, D])}
    {b b' : ofType (Φ := Φ) (Silmaril.product X S) ⟶
      ofType (Silmaril.product X D) ⨿ ofType (Silmaril.product X S)}
    (ee : (projection Seed).map e = (projection Seed).map e')
    (eb : (projection Seed).map b = (projection Seed).map b') :
    (projection Seed).map (canonicalAssembly e b) = (projection Seed).map (canonicalAssembly e' b') :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.canonicalAssembly_map_congr
    Seed ee eb

/-- The canonical choice satisfies the computation-category Elgot equations. -/
theorem canonicalElgotCategory [HasFiniteCoproducts Comp] :
    letI : Iteration Comp := canonicalIteration
    ElgotCategory Comp := by
  let : Iteration Comp := canonicalIteration
  exact ⟨Paper.TypeCategory.iterate_fixpoint, Paper.TypeCategory.iterate_naturality,
    Paper.TypeCategory.iterate_codiagonal⟩

section StepFactor

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp] [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  (J : V ⥤ Comp) [DistributiveFreydCategory J]
  (M : TypeModel τ V) (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {X S D : τ}

/-- Factor the actual carried step before comparing its retained block with syntax. -/
theorem carriedStep_factor_retained
    (b : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    carriedStep J M objIso X S D b =
      capturePrefix J M objIso X S ≫
        reindexHom J M objIso (J.map (M.productIso X (product X S)).hom ≫
          retainLeft J (R := M.obj X) b ≫ J.map (M.productIso X (packedExitType [S, D])).inv) ≫
        carriedRoute J M objIso X S D :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.carriedStep_factor_retained
    J M objIso b

/-- Factor the carried step around the transported left whiskering of the block. -/
theorem carriedStep_factor
    (whisker : ∀ {Y A B : τ} (f : J.obj (M.obj A) ⟶ J.obj (M.obj B)),
      reindexHom J M objIso (J.map (M.productIso Y A).hom ≫ retainLeft J (R := M.obj Y) f ≫
        J.map (M.productIso Y B).inv) =
        whiskerLeft (ofType (Φ := Φ) Y) (reindexHom J M objIso f))
    (b : J.obj (M.obj (product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))) :
    carriedStep J M objIso X S D b =
      capturePrefix J M objIso X S ≫ whiskerLeft (ofType X) (reindexHom J M objIso b) ≫
        carriedRoute J M objIso X S D :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.carriedStep_factor J M objIso whisker b

end StepFactor

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory Comp] [SymmetricPremonoidalCategory Comp]
  [HasFiniteCoproducts V] [HasFiniteCoproducts Comp]
  [DistributiveTensor V] [DistributivePremonoidalCategory Comp]
  [Iteration Comp] [ElgotCategory Comp] (J : V ⥤ Comp) [StrongElgotFreydCategory J]

/-- Compare retained iteration at the actual carried step before dropping the capture. -/
theorem contextualLoop_compare {E S D : V} (body : J.obj (E ⊗ S) ⟶ J.obj (D ⨿ S))
    {S' D' : Comp} (state : J.obj (E ⊗ S) ≅ S') (result : J.obj (E ⊗ D) ≅ D')
    (preserves : PreservesLoop (contextualStep J body)) :
    state.inv ≫ contextualLoop J body =
      Paper.TypeCategory.iterate (reindexStep state result (contextualStep J body)) ≫
        result.inv ≫ J.map (CartesianMonoidalCategory.snd E D) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.contextualLoop_compare
    J body state result preserves

variable (M : TypeModel τ V) [InstructionModel J M Φ]
  (objIso : ∀ A : τ, J.obj (M.obj A) ≅ ofType (Φ := Φ) A)
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Structural model comparisons preserve exact-sum dispatch. -/
theorem dispatch_compare (cmp : ModelComparisons J M objIso pe) {X A B D : τ}
    (f : J.obj (M.obj X) ⟶ J.obj (M.obj (Silmaril.coprod A B)))
    (g : J.obj (M.obj (Silmaril.product X A)) ⟶ J.obj (M.obj D))
    (h : J.obj (M.obj (Silmaril.product X B)) ⟶ J.obj (M.obj D)) :
    reindexHom J M objIso (caseWithContext J
      (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (M.productIso X A).inv ≫ g) (J.map (M.productIso X B).inv ≫ h)) =
      dispatchArrow (reindexHom J M objIso f)
        (reindexHom J M objIso g) (reindexHom J M objIso h) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.dispatch_compare
    J M objIso pe cmp f g h

/-- Compare the two-label decoder using the injections and uniqueness from empty. -/
theorem exitSum_compare (cmp : ModelComparisons J M objIso pe) (S D : τ) :
    reindexHom J M objIso (J.map (exitSum M S D)) = exitSumArrow (Φ := Φ) S D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.exitSum_compare
    J M objIso pe cmp S D

/-- The model assembly has its canonical Paper form under local loop preservation. -/
theorem compare_assemble (cmp : ModelComparisons J M objIso pe) {X S D : τ}
    (e : J.obj (M.obj X) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (b : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D])))
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D b))) :
    reindexHom J M objIso (assemble J M X S D (Silmaril.product X S)
        (((λ_ (M.obj X)).hom ▷ M.obj S) ≫ (M.productIso X S).inv) e b) =
      canonicalAssembly (reindexHom J M objIso e) (carriedStep J M objIso X S D b) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.compare_assemble
    J M objIso pe cmp e b choice

/-- The carried step respects the projected comparison of the original packed block. -/
theorem carriedStep_map_congr (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) {X S D : τ}
    {b b' : J.obj (M.obj (Silmaril.product X S)) ⟶ J.obj (M.obj (packedExitType [S, D]))}
    (e : (Paper.Extension.Singleton.projection Seed).map (reindexHom J M objIso b) =
        (Paper.Extension.Singleton.projection Seed).map (reindexHom J M objIso b')) :
    (Paper.Extension.Singleton.projection Seed).map (carriedStep J M objIso X S D b) =
      (Paper.Extension.Singleton.projection Seed).map (carriedStep J M objIso X S D b') :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.carriedStep_map_congr
    J M objIso pe cmp Seed e

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]

/-- Reindex the guarded CFG denotation to canonical singleton arrows using
preservation at its one carried iteration step. -/
theorem compare_guardedCfg {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType)))) :
    reindexHom J M objIso (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType) =
      canonicalAssembly (reindexHom J M objIso (denoteSingletonRegion J M he.hasType))
        (carriedStep J M objIso X S D (denoteSingletonRegion J M hb.hasType)) := by
  rw [denote_guardedCfg J M he hb]
  exact compare_assemble J M objIso pe cmp _ _ choice

set_option backward.isDefEq.respectTransparency false in
/-- Reify the guarded one-block denotation in the extension quotient from
the projected comparisons of its packed singleton entry and block. The
result is the explicit canonical region with a representative of the
carried step. -/
theorem reify_guardedCfg {X S D : τ} {e b : Region Φ}
    (cmp : ModelComparisons J M objIso pe)
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]])
    (choice : PreservesLoop (contextualStep J (blockComputation M J X S D
      (denoteSingletonRegion J M hb.hasType))))
    (entryIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M he.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed he)
    (blockIH : (projection Seed).map (reindexHom J M objIso (denoteSingletonRegion J M hb.hasType)) =
      Paper.Extension.Singleton.ofRegion Seed hb) :
    ∃ (step : Region Φ) (hs : ValueBranches [Silmaril.product X S] step
        [Silmaril.coprod (Silmaril.product X D) (Silmaril.product X S)]),
      carriedStep J M objIso X S D ((objIso (Silmaril.product X S)).hom ≫
        ofRegion (τ := τ) hb ≫ (objIso (packedExitType [S, D])).inv) =
          ofRegion (τ := τ) hs ≫ (sumIso (Silmaril.product X D) (Silmaril.product X S)).hom ∧
      (projection Seed).map (reindexHom J M objIso
        (denoteSingletonRegion J M (guardedCfg_typed he hb).hasType)) =
        Paper.Extension.Singleton.ofRegion Seed (canonicalRegion_typed he hs) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgAssembly.reify_guardedCfg
    J M objIso pe cmp Seed he hb choice entryIH blockIH

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
