module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs

open CategoryTheory CategoryTheory.PremonoidalCategory
open Silmaril.Thesis.LambdaIter (Sig)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

local notation "bindArrow" => ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

theorem packedNative_let1 (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B) :
    packedNative pe (.let₁ d e) =
      bindArrow (values (signature (τ := τ) (Φ := Φ) pe)) (packedNative pe d) (packedNative pe e) := by
  let J := values (signature (τ := τ) (Φ := Φ) pe)
  unfold packedNative
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
      bindArrow J (denoteInSyntax pe d)
        (J.map (envSnocIso (typeModel (Φ := Φ) pe) (Ctx.nil : Ctx Empty τ) β A).hom ≫
          denoteInSyntax pe e) = _
  rw [← bind_pre_map, ← Category.assoc, ← Functor.map_comp, packedEnvInv_snoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bind_values {S : Sig.{u}} {X A B : ValueCat S}
    (f : X.obj ⟶ A.obj) (g : (X ⊗ A).obj ⟶ B.obj) :
    bindArrow (values S) f g = pairArrows (𝟙 X.obj) f ≫ g := by
  unfold ProofRelevant.Semantics.Categorical.bind ProofRelevant.Semantics.Categorical.extend
    ProofRelevant.Semantics.Categorical.duplicate
  have hmap : (values S).map (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) =
      pairArrows (𝟙 X.obj) (𝟙 X.obj) := valueLift_hom (𝟙 X) (𝟙 X)
  have hi : (Functor.StrongPremonoidal.tensorIso (J := values S) X X).inv = 𝟙 _ := by rfl
  have hh : (Functor.StrongPremonoidal.tensorIso (J := values S) X A).hom = 𝟙 _ := by rfl
  rw [hmap, hi, hh]
  change (pairArrows (𝟙 X.obj) (𝟙 X.obj) ≫ 𝟙 _ ≫
    leftTensor (𝟙 X.obj) f ≫ 𝟙 _) ≫ g = _
  simp only [Category.id_comp, Category.comp_id, leftTensor, id_whiskerRight, Category.assoc]
  change pairArrows (𝟙 X.obj) (𝟙 X.obj) ≫ tensorLeft X.obj f ≫ g = _
  rw [← Category.assoc, tensorLeft_pair (isPureMor_id _) (isPureMor_id _), Category.id_comp]

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_let1_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) A) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.let₁ d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.let₁ ha hb) := by
  rw [packedNative_let1, ih₁, ih₂, packedArrow_let1]
  let S := signature (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  exact @bind_values S X Y Z (packedArrow ha) (packedArrow hb)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs
