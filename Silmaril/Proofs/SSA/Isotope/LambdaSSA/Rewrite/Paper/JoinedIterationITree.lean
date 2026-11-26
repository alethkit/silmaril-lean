module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.Iteration.Thms

/-! # Interpretation of joined one-block feedback in weak interaction trees -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationITree

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Region Region.SyntacticCategory

universe v w

variable {E : Type w → Type w} {Φ : Type v}

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.Semantics (encodeValue)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Region.Paper.WithProjectionReturnsAndUnitEta (Step denoteArrow denoteITree denoteITree_tree denoteArrow_canonicalIterate)
open Region.Paper.WithProjectionReturnsAndUnitEta.Reification
  (canonicalIterate canonicalIterate_ofRegion)
open Region.Paper.Extension.Singleton (ofRegion ofType sumIso)

variable {κ : Type (w + 1)} [AtomValues κ] [HasTy Φ (Ty κ)] [HasEff Φ Bool]
attribute [local instance] typeModel categoricalInstructions
variable [InstructionModel Φ (Ty κ) Bool (ModelTree E)]

set_option hygiene false in
local notation "TypedCalls" => ⟨fun f x =>
  InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree E) f x⟩
local notation "V" => AtomValues.carrier (κ := κ)
local notation "Raw" => Sigma V
local notation "Seed" => Step (τ := Ty κ) (Φ := Φ)
local notation "TM" => ModelTree E
local notation "K" => typeJ (m := ModelTree E)
local notation "M" => Silmaril.Isotope.LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Ty κ)

theorem iterationTree
    (instr : Primitive E Φ Raw) (compat : Compatible (κ' := κ) TypedCalls instr)
    {A B : Ty κ} {r : Region Φ} (hr : ValueBranches [A] r [Silmaril.coprod B A])
    (a : Ty.denote V A) (env : Env Raw) :
    (denoteITree instr compat
      (canonicalIterate (ofRegion Seed hr ≫ (sumIso Seed B A).hom)) a >>=
        fun b => pure (0, encodeValue V B b)) =
      region instr (extend env (encodeValue V A a)) (iterateRegion A r) := by
  rw [canonicalIterate_ofRegion hr]
  exact denoteITree_tree instr compat (iterateRegion_valueBranches hr) a env

set_option backward.isDefEq.respectTransparency false in
private theorem exactSum_comp_coprodIsoSum (A B : Ty κ) :
    (Paper.TypeCategory.denoteExactSumIso (K) (M) A B).hom ≫
      (Kleisli.Type.coprodIsoSum (TM) ((K).obj ((M).obj A)) ((K).obj ((M).obj B))).hom =
        𝟙 ((K).obj ((M).obj (Silmaril.coprod A B))) := by
  let comparison := asIso (coprodComparison (K) ((M).obj A) ((M).obj B))
  let typeSum := Types.binaryCoproductIso ((M).obj A) ((M).obj B)
  have chosen :
      comparison.hom ≫ (K).map typeSum.hom =
        (Kleisli.Type.coprodIsoSum (TM) ((K).obj ((M).obj A)) ((K).obj ((M).obj B))).hom := by
    apply coprod.hom_ext
    · simp only [comparison, asIso_hom, coprodComparison, coprod.inl_desc_assoc,
        Kleisli.Type.inl_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
      rw [Types.binaryCoproductIso_inl_comp_hom]
      rfl
    · simp only [comparison, asIso_hom, coprodComparison, coprod.inr_desc_assoc,
        Kleisli.Type.inr_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
      rw [Types.binaryCoproductIso_inr_comp_hom]
      rfl
  change (((K).map ((M).coprodIso A B).hom) ≫ comparison.inv) ≫ _ = _
  rw [← chosen, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  have decoded : ((M).coprodIso A B).hom ≫ typeSum.hom = 𝟙 _ := by
    change (𝟙 _ ≫ typeSum.inv) ≫ typeSum.hom = 𝟙 _
    rw [Category.id_comp, Iso.inv_hom_id]
  rw [decoded]
  exact (K).map_id _

set_option backward.isDefEq.respectTransparency false in
theorem typedIterate
    (instr : Primitive E Φ Raw) (compat : Compatible (κ' := κ) TypedCalls instr)
    {A B : Ty κ} (f : ofType Seed A ⟶ ofType Seed B ⨿ ofType Seed A) (a : Ty.denote V A) :
    denoteITree instr compat (canonicalIterate f) a =
      Silmaril.Elgot.iter (denoteITree instr compat (f ≫ (sumIso Seed B A).inv)) a := by
  let := regionTypingCoherent instr compat
  let shared : ∀ X Y : Type (w + 1),
      ∃ h : (K).obj X ⊗ (K).obj Y = (K).obj (X ⊗ Y),
        Functor.StrongPremonoidal.tensorIso (J := K) X Y = eqToIso h := fun _ _ => ⟨rfl, rfl⟩
  let step := denoteArrow (K) (M) shared (f ≫ (sumIso Seed B A).inv)
  have preserved := denoteArrow_canonicalIterate (K) (M) shared f
  calc
    _ = (CategoryTheory.iterate (step ≫ (Paper.TypeCategory.denoteExactSumIso (K) (M) B A).hom)).of a :=
      congrArg (fun g : (K).obj ((M).obj A) ⟶ (K).obj ((M).obj B) => g.of a) preserved
    _ = _ := by
      rw [Kleisli.Type.iterate_of, Category.assoc, exactSum_comp_coprodIsoSum, Category.comp_id]
      rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedIterationITree
