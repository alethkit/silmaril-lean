module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReification

/-! # Denotation of the actual one-block CFG through its two packed arrows -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Paper.PackedBody (applyPacked applyPacked_typed)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open SingletonDispatcher (denoteSingleCfg)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

section Congruence

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

omit [TypeFormers τ] in
/-- Keep the singleton label when adding fresh labels after it. -/
private theorem keepHead (P : τ) (L : LCtx τ) : Ren [P] (P :: L) id := by
  intro i A hi
  cases i with
  | zero => exact hi
  | succ i => simp [At] at hi

set_option backward.isDefEq.respectTransparency false in
/-- The linked decoder preserves the constructor-valued branch boundary. -/
theorem decodeExits_typed {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (h : ValueBranches Γ r [packedExitType L]) : ValueBranches Γ (decodeExits r L) L := by
  let P := packedExitType L
  have hrename {Δ : VCtx τ} {K K' : LCtx τ} {p : Region Φ}
      (hp : ValueBranches Δ p K) {ρ : Nat → Nat} (hρ : Ren K K' ρ) :
      ValueBranches Δ (p.renameLabels ρ) K' := by
    rw [renameLabels_eq_lsubst]
    exact hp.lsubst (fun _ _ hi => .br (hρ hi) (.var rfl))
  refine .cfg (fun _ : Fin 1 => P) ?_ (fun _ => ?_)
  · change ValueBranches Γ r (P :: L)
    simpa only [renameLabels_id] using hrename h (keepHead P L)
  · change ValueBranches (P :: Γ) ((unpackExits L).renameLabels (fun j => 1 + j)) (P :: L)
    simp only [Nat.one_add]
    exact hrename ((unpackExits_valueFamily Γ L) (ℓ := 0) (A := P) rfl) (Ren.wk L P)

theorem guardedCfg_typed {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    ValueBranches [X] (guardedCfg S D e b) [D] :=
  .cfg (fun _ : Fin 1 => S) (decodeExits_typed he)
    (fun _ => decodeExits_typed (applyPacked_typed hb))

set_option backward.isDefEq.respectTransparency false in
private theorem decode_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Paper.Extension.Eqv Seed Γ r s [packedExitType L]) :
    Paper.Extension.Eqv Seed Γ (decodeExits r L) (decodeExits s L) L := by
  refine .cfg (fun _ : Fin 1 => packedExitType L) ?_ (fun _ => ?_)
  · change Paper.Extension.Eqv Seed Γ r s (packedExitType L :: L)
    simpa only [renameLabels_id] using h.renameLabels (keepHead (packedExitType L) L)
  · let P := packedExitType L
    change Paper.Extension.Eqv Seed (P :: Γ)
      ((unpackExits L).renameLabels (fun j => 1 + j)) ((unpackExits L).renameLabels (fun j => 1 + j)) (P :: L)
    simp only [Nat.one_add]
    exact .refl (((unpackExits_valueFamily Γ L) (ℓ := 0) (A := P) rfl).hasType.renameLabels (Ren.wk L P))

set_option backward.isDefEq.respectTransparency false in
theorem guardedCfg_congr {X S D : τ} {e e' b b' : Region Φ}
    (he : Paper.Extension.Eqv Seed [X] e e' [packedExitType [S, D]])
    (hb : Paper.Extension.Eqv Seed [Silmaril.product X S] b b' [packedExitType [S, D]]) :
    Paper.Extension.Eqv Seed [X] (guardedCfg S D e b) (guardedCfg S D e' b') [D] := by
  refine .cfg (fun _ : Fin 1 => S) (decode_congr Seed he) (fun _ => decode_congr Seed ?_)
  apply hb.substVars
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  | succ i => simp [At] at hi

end Congruence

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem packed_exits {X : τ} {L : LCtx τ} {r : Region Φ}
    (h : HasType [X] r L)
    (hp : HasType [X] (packLocalExits r L) [packedExitType L]) :
    J.map ((λ_ (M.obj X)).hom) ≫ denoteSingletonRegion J M hp ≫ J.map (unpackLabel M L) =
      denoteRegion J M h := by
  have cancel : packLabelExit M L ≫ singletonLabelPayload M (packedExitType L) ≫ unpackLabel M L =
      𝟙 _ := packLabelExit_unpackLabelExit M L
  rw [denoteSingletonRegion, denoteRegion_linkPackExits J M h hp]
  simp only [Category.assoc, ← J.map_comp_assoc, ← J.map_comp, Iso.hom_inv_id, J.map_id,
    Category.id_comp, cancel, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc] private theorem packed_block {S X D : τ} {b : Region Φ} (hb : HasType [S, X] b [S, D]) :
    J.map (inputRecordIso M [S, X]).hom ≫ denoteSingletonRegion J M (block_typed hb) ≫
      J.map (unpackLabel M [S, D]) = denoteRegion J M hb := by
  have h := packed_exits J M hb.packInputs (block_typed hb)
  rw [denoteRegion_packInputs J M hb] at h
  have hh := congrArg (J.map (packedInputIso M [S, X]).hom ≫ ·) h
  rw [← Category.assoc, ← J.map_comp,
    ← J.map_comp_assoc, Iso.hom_inv_id, J.map_id, Category.id_comp] at hh
  simpa only [packedInputIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
theorem denote_cfg {X S D : τ} {e b : Region Φ}
    (he : HasType [X] e [S, D]) (hb : HasType [S, X] b [S, D]) :
    denoteSingletonRegion J M (.cfg (fun _ : Fin 1 => S) he (fun _ => hb)) =
      assemble J M X S D (packedInputType [S, X]) (inputRecordIso M [S, X]).hom
        (denoteSingletonRegion J M (entry_typed he))
        (denoteSingletonRegion J M (block_typed hb)) := by
  rw [denoteSingletonRegion, denoteSingleCfg M J he hb, assemble]
  simp only [J.map_comp, Category.assoc, packed_exits_assoc J M he (entry_typed he),
    packed_block_assoc J M hb]

set_option backward.isDefEq.respectTransparency false in
omit [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M] in
@[reassoc] private theorem strip_singleton_input {X D : τ} {e : Region Φ}
    (he : HasType [X] e [D]) :
    J.map ((λ_ (M.obj X)).hom) ≫ denoteSingletonRegion J M he =
      denoteRegion J M he ≫ J.map (singletonLabelPayload M D) := by
  simp only [denoteSingletonRegion, ← J.map_comp_assoc, Iso.hom_inv_id, J.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
theorem denote_guardedCfg {X S D : τ} {e b : Region Φ}
    (he : ValueBranches [X] e [packedExitType [S, D]])
    (hb : ValueBranches [Silmaril.product X S] b [packedExitType [S, D]]) :
    denoteSingletonRegion J M (guardedCfg_typed he hb).hasType =
      assemble J M X S D (Silmaril.product X S)
        (((λ_ (M.obj X)).hom ▷ M.obj S) ≫ (M.productIso X S).inv)
        (denoteSingletonRegion J M he.hasType) (denoteSingletonRegion J M hb.hasType) := by
  let ht := (applyPacked_typed hb).hasType
  let hE := (decodeExits_typed he).hasType
  let hB := (decodeExits_typed (applyPacked_typed hb)).hasType
  change denoteSingletonRegion J M (.cfg (fun _ : Fin 1 => S) hE (fun _ => hB)) = _
  rw [denoteSingletonRegion, denoteSingleCfg M J hE hB, assemble,
    denoteRegion_linkUnpackExits J M he.hasType hE, denoteRegion_linkUnpackExits J M ht hB]
  simp only [unpackLabelExit, J.map_comp, Category.assoc, strip_singleton_input_assoc J M,
    SingletonReification.denote_applyPacked_assoc J M hb]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonCfgReification
