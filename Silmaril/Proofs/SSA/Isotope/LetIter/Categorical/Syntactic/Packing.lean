module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
import Silmaril.SSA.Isotope.Bridge.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory CartesianMonoidalCategory
open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.Syn (mk)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

open ProofRelevant.Semantics.Categorical (extend retainLeft)
local notation "pairArrow" => ProofRelevant.Semantics.Categorical.pair
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

private theorem fst_transport {V : Type u} [Category* V] [CartesianMonoidalCategory V]
    {X Y : V} (e : X = Y) (A : V) :
    eqToHom (congrArg (fun Z => Z ⊗ A) e).symm ≫ CartesianMonoidalCategory.fst X A =
      CartesianMonoidalCategory.fst Y A ≫ eqToHom e.symm := by
  subst Y
  simp

private theorem snd_transport {V : Type u} [Category* V] [CartesianMonoidalCategory V]
    {X Y : V} (e : X = Y) (A : V) :
    eqToHom (congrArg (fun Z => Z ⊗ A) e).symm ≫ CartesianMonoidalCategory.snd X A =
      CartesianMonoidalCategory.snd Y A := by
  subst Y
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem packedBoundLookup (pe : ε) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    let S := signature (τ := τ) (Φ := Φ) pe
    (values S).map (eqToHom (boundObj_eq (Φ := Φ) pe β).symm ≫
        boundLookup (typeModel (Φ := Φ) pe) i) ≫
      eqToHom (congrArg (fun A : τ => of (S := S) A) (Bridge.BoundCtx.get_toThesis β i).symm) =
      packedArrow (S := S) (HasType.bv (β := Bridge.BoundCtx.toThesis β) (ι := i)) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · refine Eq.trans ?_ (packedArrow_bv_zero (S := S) (Bridge.BoundCtx.toThesis β) A).symm
      let E := boundObj_eq (Φ := Φ) pe β
      let Y := valueObj (Φ := Φ) pe A
      change J.map (eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
        CartesianMonoidalCategory.snd (boundObj M β) Y) ≫ 𝟙 _ =
          J.map (CartesianMonoidalCategory.snd _ Y)
      rw [Category.comp_id]
      exact congrArg J.map (snd_transport E Y)
    · refine Eq.trans ?_ (packedArrow_bv_succ (S := S) (Bridge.BoundCtx.toThesis β) A j).symm
      let E := boundObj_eq (Φ := Φ) pe β
      let Y := valueObj (Φ := Φ) pe A
      let resultCast := eqToHom (congrArg (fun A : τ => J.obj (M.obj A))
        (Bridge.BoundCtx.get_toThesis β j).symm)
      change J.map (eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
        (CartesianMonoidalCategory.fst (boundObj M β) Y ≫ boundLookup M j)) ≫ resultCast = _
      have moveProjection :
          eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
              (CartesianMonoidalCategory.fst (boundObj M β) Y ≫ boundLookup M j) =
            CartesianMonoidalCategory.fst _ Y ≫ (eqToHom E.symm ≫ boundLookup M j) := by
        rw [← Category.assoc, fst_transport E Y, Category.assoc]
      calc
        _ = J.map (CartesianMonoidalCategory.fst _ Y ≫ (eqToHom E.symm ≫ boundLookup M j)) ≫
            resultCast := congrArg (fun f => J.map f ≫ resultCast) moveProjection
        _ = J.map (CartesianMonoidalCategory.fst _ Y) ≫
            (J.map (eqToHom E.symm ≫ boundLookup M j) ≫ resultCast) := by
          rw [J.map_comp, Category.assoc]
        _ = _ := congrArg (fun f => J.map (CartesianMonoidalCategory.fst _ Y) ≫ f) (ih j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_bv_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} (i : Fin n)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (.bv i) (β.get i)) :
    packedNative pe (Derivation.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (ι := i) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
    J.map (boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := β) i) = _
  rw [← J.map_comp, packedEnvInv_boundVar]
  have castPacked : ∀ {A : τ} (e : (Bridge.BoundCtx.toThesis β).get i = A)
      (k : HasType S.Instr .nil (Bridge.BoundCtx.toThesis β) (.bv i) A),
      packedArrow (S := S) (HasType.bv (ι := i)) ≫ eqToHom (congrArg (of (S := S)) e) =
        packedArrow (S := S) k := by
    intro A e k
    subst A
    rw [eqToHom_refl, Category.comp_id]
    rfl
  have e := Bridge.BoundCtx.get_toThesis β i
  rw [← castPacked e h, ← packedBoundLookup pe β i]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_unit_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) .unit (Silmaril.unit : τ)) :
    packedNative pe (Derivation.unit (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h := by
  cases h
  let _ := Bridge.thesisHasEff Φ ε
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let toUnit : X ⟶ 𝟙_ (ValueCat S) :=
    ⟨mk (S := S) HasType.unit, ⟨.unit, .unit, .unit, rfl⟩⟩
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
    J.map (CartesianMonoidalCategory.toUnit _ ≫ (typeModel (Φ := Φ) pe).unitIso.inv) = J.map toUnit
  rw [← J.map_comp]
  exact congrArg J.map (CartesianMonoidalCategory.toUnit_unique _ _)

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inl_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inl (B := B) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inl (B := B) h) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let comparison := M.coprodIso A B
  have injection : coprod.inl ≫ comparison.inv =
      (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inl := by
    rw [← valueInl_coprodIso pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = packedNative pe d ≫ J.map (coprod.inl ≫ comparison.inv) :=
      (Category.assoc _ _ _).symm
    _ = packedNative pe d ≫ injl (of (S := S) A) (of B) :=
      congrArg (fun f => packedNative pe d ≫ J.map f) injection
    _ = packedArrow (S := S) h ≫ injl (of (S := S) A) (of B) :=
      congrArg (fun f => f ≫ injl (of (S := S) A) (of B)) ih
    _ = _ := (packedArrow_inl (S := S) h).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inr_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t B)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) B)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inr (A := A) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inr (A := A) h) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let comparison := M.coprodIso A B
  have injection : coprod.inr ≫ comparison.inv =
      (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inr := by
    rw [← valueInr_coprodIso pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = packedNative pe d ≫ J.map (coprod.inr ≫ comparison.inv) :=
      (Category.assoc _ _ _).symm
    _ = packedNative pe d ≫ injr (of (S := S) A) (of B) :=
      congrArg (fun f => packedNative pe d ≫ J.map f) injection
    _ = packedArrow (S := S) h ≫ injr (of (S := S) A) (of B) :=
      congrArg (fun f => f ≫ injr (of (S := S) A) (of B)) ih
    _ = _ := (packedArrow_inr (S := S) h).symm

private theorem retainLeft_values {S : Sig.{u}} {R A B : ValueCat S}
    (f : A.obj ⟶ B.obj) :
    retainLeft (values S) (R := R) f = tensorLeft R.obj f := by
  change 𝟙 _ ≫ leftTensor (𝟙 R.obj) f ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id, leftTensor, id_whiskerRight]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bind_pair_pure_left {S : Sig.{u}} {X A B : ValueCat S}
    (p : X ⟶ A) (g : X.obj ⟶ B.obj) :
    bindArrow (values S) g ((values S).map (p ▷ B)) = pairArrows p.hom g := by
  let J := values S
  have retain : extend J g = J.map (lift (𝟙 X) (𝟙 X)) ≫ retainLeft J (R := X) g := by
    rw [← extend_map J (𝟙 X)]
    calc
      _ = extend J (𝟙 (J.obj X) ≫ g) := congrArg (extend J) (Category.id_comp g).symm
      _ = extend J (𝟙 (J.obj X)) ≫ retainLeft J g := extend_comp J (𝟙 (J.obj X)) g
      _ = _ := congrArg (fun k => extend J k ≫ retainLeft J g) (J.map_id X).symm
  have diagonal : lift (𝟙 X) (𝟙 X) ≫ (p ▷ X) = lift p (𝟙 X) := by
    apply hom_ext <;> simp
  unfold ProofRelevant.Semantics.Categorical.bind
  rw [retain, Category.assoc, ← retainLeft_pre_map J p g, ← Category.assoc, ← J.map_comp,
    diagonal, retainLeft_values]
  have mapLift : J.map (lift p (𝟙 X)) = pairArrows p.hom (𝟙 X.obj) := valueLift_hom p (𝟙 X)
  rw [mapLift]
  rw [tensorLeft_pair p.property (isPureMor_id _), Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_values {S : Sig.{u}} {X A B : ValueCat S}
    (f : X.obj ⟶ A.obj) (g : X.obj ⟶ B.obj) :
    pairArrow (values S) f g = pairArrows f g := by
  let J := values S
  have keepResults : lift (fst (X ⊗ A) B ≫ snd X A) (snd (X ⊗ A) B) = snd X A ▷ B := by
    apply hom_ext <;> simp
  unfold ProofRelevant.Semantics.Categorical.pair ProofRelevant.Semantics.Categorical.retainedContext
  rw [keepResults, bind_pair_pure_left, bind_values]
  exact (pairArrows_seq f g).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_pair_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) β s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.pair d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.pair ha hb) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  calc
    _ = J.map k ≫ pairArrow J (denoteInSyntax pe d) (denoteInSyntax pe e) := by
      change J.map k ≫ (pairArrow J (denoteInSyntax pe d) (denoteInSyntax pe e) ≫ 𝟙 _) = _
      rw [Category.comp_id]
    _ = pairArrow J (packedNative pe d) (packedNative pe e) :=
      (pair_pre_map J k (denoteInSyntax pe d) (denoteInSyntax pe e)).symm
    _ = pairArrows (packedNative pe d) (packedNative pe e) :=
      @pair_values S X Y Z (packedNative pe d) (packedNative pe e)
    _ = _ := (congrArg₂ pairArrows ih₁ ih₂).trans (packedArrow_pair (S := S) ha hb).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_let2 (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 2)} {A B C : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (product A B))
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc (.snoc β A) B) s C) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.let₂ d e) =
      pairArrows (𝟙 X) (packedNative pe d) ≫ (tensorAssociator X (of A) (of B)).inv ≫
        packedNative pe e := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let W := valueObj (τ := τ) (Φ := Φ) pe C
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  let q := envPairHom M (Ctx.nil : Ctx Empty τ) β A B
  let p := J.map q ≫ denoteInSyntax pe e
  have pairMap : (𝟙 (envObj M (Ctx.nil : Ctx Empty τ) β)) ⊗ₘ (M.productIso A B).hom = 𝟙 _ := by
    change (𝟙 _) ⊗ₘ (𝟙 _) = 𝟙 _
    simp
  have beforeBind : packedNative pe (.let₂ d e) =
      J.map k ≫ bindArrow J (denoteInSyntax pe d) p := by
    change J.map k ≫ bindArrow J (denoteInSyntax pe d)
      (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫ p) = _
    have mapId := (congrArg J.map pairMap).trans (J.map_id _)
    exact congrArg (fun f => J.map k ≫ bindArrow J (denoteInSyntax pe d) f)
      ((congrArg (fun f => f ≫ p) mapId).trans (Category.id_comp p))
  have afterSplit :
      J.map (k ▷ (Y ⊗ Z)) ≫ p =
        J.map (α_ X Y Z).inv ≫ packedNative pe e := by
    unfold p packedNative
    rw [← J.map_comp_assoc, packedEnvInv_pair, J.map_comp, Category.assoc]
  calc
    _ = J.map k ≫ bindArrow J (denoteInSyntax pe d) p := beforeBind
    _ = bindArrow J (packedNative pe d) (J.map (k ▷ (Y ⊗ Z)) ≫ p) :=
      (bind_pre_map J k (denoteInSyntax pe d) p).symm
    _ = bindArrow J (packedNative pe d) (J.map (α_ X Y Z).inv ≫ packedNative pe e) :=
      congrArg (bindArrow J (packedNative pe d)) afterSplit
    _ = _ := @bind_values S X (Y ⊗ Z) W (packedNative pe d)
      (J.map (α_ X Y Z).inv ≫ packedNative pe e)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs
