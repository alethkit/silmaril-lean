module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Defs

/-! # Packed dispatch selects the specified flat block -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.ContinuationContext
open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}

local notation "Ctx" => ContinuationContext Φ ([] : VCtx τ)

private theorem packedExitArg_rename (i : Nat) (a : Tm Φ) (ρ : Nat → Nat) :
    (packedExitArg i a).rename ρ = packedExitArg i (a.rename ρ) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [packedExitArg, Tm.rename, ih]

theorem liftLSubstVars_routeExit (blocks : Nat) :
    liftLSubstVars (routeExit (Φ := Φ) blocks) = routeExit blocks := by
  funext i
  simp only [liftLSubstVars, routeExit]
  split <;> simp only [Region.renameVars, Tm.rename, packedExitArg_rename, Silmaril.DeBruijn.lift]

theorem routedBlock_valueBranches {g : FiniteCFG Φ blocks exits 0} (hg : FiniteCFG.HasType .nil R E g)
    (i : Fin blocks) :
    ValueBranches [R i] (routedFlat blocks (g.block i))
      [Silmaril.coprod (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))] := by
  let body : ContinuationFamily (Φ := Φ) [] [R i] (List.ofFn R ++ List.ofFn E) :=
    ⟨fun _ => (g.block i).erase.bindBranchArguments, fun _ _ hi =>
      (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ blockValueBranches hg i⟩
  have typed := (body.compose (routeFamily (List.ofFn R) (List.ofFn E))).property
    (show At [R i] 0 (R i) from rfl)
  simpa only [routedFlat, body, ContinuationFamily.compose, compLSubst, routeFamily, List.length_ofFn,
    liftLSubstVars_routeExit] using typed

theorem blockStep_ofRegion {g : FiniteCFG Φ blocks exits 0} (hg : FiniteCFG.HasType .nil R E g)
    (i : Fin blocks) :
    blockStep hg i = Paper.TypeCategory.ofRegion (routedBlock_valueBranches hg i) ≫
      (Paper.TypeCategory.sumIso (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))).hom := by
  let out := Silmaril.coprod (packedExitType (List.ofFn E)) (packedExitType (List.ofFn R))
  have selected :
      singletonToHom (Y := (⟨List.ofFn R ++ List.ofFn E⟩ : Ctx)) (blockValueBranches hg i) ≫
        (routeFamily (List.ofFn R) (List.ofFn E)).toHom (Y := single out) =
      singletonToHom (Y := (single out : Ctx)) (routedBlock_valueBranches hg i) := by
    unfold singletonToHom
    erw [← ContinuationFamily.compose_toHom]
    apply congrArg (ContinuationFamily.toHom (X := single (R i)) (Y := (single out : Ctx)))
    apply Subtype.ext
    funext _
    simp only [routedFlat, ContinuationFamily.compose, compLSubst, routeFamily, List.length_ofFn,
      liftLSubstVars_routeExit]
  erw [blockStep, selected]
  rfl

@[reassoc] theorem packLabels_unpackLabels (L : LCtx τ) :
    packLabels (Φ := Φ) L ≫ unpackLabels L = 𝟙 (⟨L⟩ : Ctx) := by
  rw [packLabels, unpackLabels, ← ContinuationFamily.compose_toHom, ← ContinuationFamily.identity_toHom]
  exact ContinuationFamily.toHom_eq_iff.mpr (unpack_packExits_pointwise [] L)

theorem selectLabel_comp_family {L K : LCtx τ} {i : Nat} {A : τ} (hi : At L i A)
    (σ : ContinuationFamily (Φ := Φ) [] L K) :
    selectLabel hi ≫ ContinuationFamily.toHom (X := (⟨L⟩ : Ctx)) (Y := ⟨K⟩) σ =
      singletonToHom (Y := (⟨K⟩ : Ctx)) (σ.property hi) := by
  unfold selectLabel singletonToHom
  rw [← ContinuationFamily.compose_toHom]
  apply congrArg (ContinuationFamily.toHom (X := single A) (Y := (⟨K⟩ : Ctx)))
  apply Subtype.ext
  funext _
  exact congrFun (compLSubst_id_left σ.val) i

theorem selectLabel_blockFamily {g : FiniteCFG Φ blocks exits 0} (hg : FiniteCFG.HasType .nil R E g)
    (i : Fin blocks) :
    selectLabel (SSA.FiniteSum.at_ofFn R i) ≫ (blockFamily hg).toHom =
      singletonToHom (Y := (⟨List.ofFn R ++ List.ofFn E⟩ : Ctx)) (blockValueBranches hg i) := by
  erw [selectLabel_comp_family]
  unfold singletonToHom
  apply congrArg (ContinuationFamily.toHom (X := single (R i)) (Y := (⟨List.ofFn R ++ List.ofFn E⟩ : Ctx)))
  apply Subtype.ext
  funext _
  simp [blockFamily, ContinuationFamily.ofTyped, i.isLt]

theorem packedBlockIn_ofRegion (i : Fin blocks) :
    packedBlockIn (Φ := Φ) (R := R) i =
      Paper.TypeCategory.ofRegion ((packExits_valueFamily [] (List.ofFn R)) (SSA.FiniteSum.at_ofFn R i)) := by
  erw [packedBlockIn, packLabels, selectLabel_comp_family]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem packedBlockIn_dispatcher {g : FiniteCFG Φ blocks exits 0} (hg : FiniteCFG.HasType .nil R E g)
    (i : Fin blocks) :
    packedBlockIn i ≫ packedDispatcher hg = blockStep hg i := by
  apply InducedCategory.hom_ext
  simp only [packedBlockIn, packedDispatcher, blockStep, InducedCategory.homMk_hom,
    InducedCategory.comp_hom, ← Category.assoc, ← Functor.map_comp]
  congr 1
  congr 1
  simp only [Category.assoc, packLabels_unpackLabels_assoc, ← selectLabel_blockFamily hg i]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatDispatcher
