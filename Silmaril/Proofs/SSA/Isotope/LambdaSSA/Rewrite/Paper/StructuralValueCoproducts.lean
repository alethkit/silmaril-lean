module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Tensor.Premonoidal.Thms

/-! # Binary coproducts and initiality for structural values -/

public section

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.StructuralValues (HomProperty ValueCategory inclusion sum_inl_mem sum_inr_mem
  pair_comp sum)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair empty_centralCopies)
open Paper.Extension.Singleton.CoproductDistributivity (whiskeredSumIsColimit whiskerLeftPreservesBinary)

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueCoproducts

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Val" => ValueCategory Seed
local notation "incl" => inclusion Seed
local notation "L" => whiskerLeft Seed
local notation "R" => whiskerRight Seed
local notation "d" => discardArrow Seed
local notation "S" => sumCofan Seed
local notation "SL" => sumCofanIsColimit Seed
local notation "H" => HomProperty Seed
local notation "E" => (Silmaril.empty : τ)
local infixr:65 " ⊕ₜ " => Silmaril.coprod

private theorem copair_inl {A B : τ} {D : Q} (f : Obj A ⟶ D) (g : Obj B ⟶ D) :
    (S A B).inl ≫ exactCopair Seed f g = f :=
  (SL A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

private theorem copair_inr {A B : τ} {D : Q} (f : Obj A ⟶ D) (g : Obj B ⟶ D) :
    (S A B).inr ≫ exactCopair Seed f g = g :=
  (SL A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

private theorem rightPreservesBinary (X : Q) :
    PreservesColimitsOfShape (Discrete WalkingPair) (whiskerRightFunctor Seed X) := by
  have := whiskerLeftPreservesBinary Seed X
  let e : whiskerLeftFunctor Seed X ≅ whiskerRightFunctor Seed X :=
    NatIso.ofComponents (braidIso Seed X) (fun f => braid_naturality_right Seed f X)
  exact preservesColimitsOfShape_of_natIso (J := Discrete WalkingPair) e

set_option backward.isDefEq.respectTransparency false in
private noncomputable def rightSumIsColimit (X : Q) (A B : τ) :
    IsColimit (BinaryCofan.map (whiskerRightFunctor Seed X) (S A B)) :=
  letI := rightPreservesBinary Seed X
  BinaryCofan.isColimitMapCoconeEquiv (isColimitOfPreserves (whiskerRightFunctor Seed X) (SL A B))

-- Each interchange square can be checked on the two injections of the appropriate whiskered sum.
set_option backward.isDefEq.respectTransparency false in
private theorem copair_central {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : H f) (hg : H g) : WhiskerCentral Seed (exactCopair Seed f g) := by
  let q := exactCopair Seed f g
  have legLeft {C : τ} (i : Obj C ⟶ Obj (A ⊕ₜ B)) (h : H i)
      {X Y : Q} (k : X ⟶ Y) (hq : H (i ≫ q)) :
      R i X ≫ R q X ≫ L D k = R i X ≫ L (Obj (A ⊕ₜ B)) k ≫ R q Y := by
    rw [← Category.assoc (R i X), ← (whiskerRightFunctor Seed X).map_comp i q,
      (hq.1.1 k).1, ← Category.assoc (R i X), (h.1.1 k).1, Category.assoc,
      ← (whiskerRightFunctor Seed Y).map_comp i q]
  have legRight {C : τ} (i : Obj C ⟶ Obj (A ⊕ₜ B)) (h : H i)
      {X Y : Q} (k : X ⟶ Y) (hq : H (i ≫ q)) :
      L X i ≫ L X q ≫ R k D = L X i ≫ R k (Obj (A ⊕ₜ B)) ≫ L Y q := by
    rw [← Category.assoc (L X i), ← (whiskerLeftFunctor Seed X).map_comp i q,
      (hq.1.1 k).2, ← Category.assoc (L X i), (h.1.1 k).2, Category.assoc,
      ← (whiskerLeftFunctor Seed Y).map_comp i q]
  have hl : H ((S A B).inl ≫ q) := (copair_inl Seed f g).symm ▸ hf
  have hr : H ((S A B).inr ≫ q) := (copair_inr Seed f g).symm ▸ hg
  intro X Y k
  exact ⟨BinaryCofan.IsColimit.hom_ext (rightSumIsColimit Seed X A B)
      (legLeft _ (sum_inl_mem Seed A B) k hl) (legLeft _ (sum_inr_mem Seed A B) k hr),
    BinaryCofan.IsColimit.hom_ext (whiskeredSumIsColimit Seed X.as A B)
      (legRight _ (sum_inl_mem Seed A B) k hl) (legRight _ (sum_inr_mem Seed A B) k hr)⟩

set_option backward.isDefEq.respectTransparency false in
theorem copair_mem {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : H f) (hg : H g) : H (exactCopair Seed f g) := by
  let q := exactCopair Seed f g
  refine ⟨⟨copair_central Seed hf hg, ?_⟩, ?_⟩
  · change pairArrows Seed q q = q ≫ diagonalArrow Seed D
    apply BinaryCofan.IsColimit.hom_ext (SL A B)
    · rw [← pair_comp Seed (S A B).inl q q (sum_inl_mem Seed A B).1,
        ← Category.assoc, copair_inl]
      exact hf.1.2
    · rw [← pair_comp Seed (S A B).inr q q (sum_inr_mem Seed A B).1,
        ← Category.assoc, copair_inr]
      exact hg.1.2
  · change q ≫ d D.as = d (A ⊕ₜ B)
    apply BinaryCofan.IsColimit.hom_ext (SL A B)
    · rw [← Category.assoc, copair_inl]
      exact hf.2.trans (sum_inl_mem Seed A B).2.symm
    · rw [← Category.assoc, copair_inr]
      exact hg.2.trans (sum_inr_mem Seed A B).2.symm

set_option backward.isDefEq.respectTransparency false in
noncomputable def sumIsColimit (A B : τ) : IsColimit (sum Seed A B) :=
  BinaryCofan.IsColimit.mk _
    (fun f g => ⟨exactCopair Seed f.hom g.hom, copair_mem Seed f.property g.property⟩)
    (fun f g => (incl).map_injective (copair_inl Seed f.hom g.hom))
    (fun f g => (incl).map_injective (copair_inr Seed f.hom g.hom))
    (fun f g _ hl hr => (incl).map_injective (BinaryCofan.IsColimit.hom_ext (SL A B)
      ((congrArg (incl).map hl).trans (copair_inl Seed f.hom g.hom).symm)
      ((congrArg (incl).map hr).trans (copair_inr Seed f.hom g.hom).symm)))

noncomputable def emptyIsInitial : IsInitial (⟨Obj E⟩ : Val) :=
  IsInitial.ofUniqueHom
    (fun Y => ⟨(Paper.Extension.Singleton.emptyIsInitial Seed).to Y.obj,
      ⟨empty_centralCopies Seed _, (Paper.Extension.Singleton.emptyIsInitial Seed).hom_ext _ _⟩⟩)
    (fun _ _ => (incl).map_injective ((Paper.Extension.Singleton.emptyIsInitial Seed).hom_ext _ _))

theorem valueHasFiniteCoproducts : HasFiniteCoproducts Val :=
  haveI : HasInitial Val := (emptyIsInitial Seed).hasInitial
  haveI : HasBinaryCoproducts Val :=
    haveI (X Y : Val) : HasBinaryCoproduct X Y :=
      ⟨⟨⟨_, sumIsColimit Seed X.obj.as Y.obj.as⟩⟩⟩
    hasBinaryCoproducts_of_hasColimit_pair _
  hasFiniteCoproducts_of_has_binary_and_initial

theorem valuePreservesFiniteCoproducts : PreservesFiniteCoproducts (incl) where
  preserves n := by
    let := valueHasFiniteCoproducts Seed
    have : PreservesColimitsOfShape (Discrete WalkingPair) (incl) :=
      { preservesColimit := fun {K} => by
          let A : τ := (K.obj ⟨WalkingPair.left⟩).obj.as
          let B : τ := (K.obj ⟨WalkingPair.right⟩).obj.as
          have hm : IsColimit (BinaryCofan.map (incl) (sum Seed A B)) := SL A B
          have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) (incl) :=
            preservesColimit_of_preserves_colimit_cocone
              (sumIsColimit Seed A B) (BinaryCofan.isColimitMapCoconeEquiv.symm hm)
          exact preservesColimit_of_iso_diagram (incl) (diagramIsoPair K).symm }
    have : PreservesColimit (Functor.empty.{0} Val) (incl) :=
      preservesColimit_of_preserves_colimit_cocone (emptyIsInitial Seed)
        ((isColimitMapCoconeEmptyCoconeEquiv (incl) _).symm (Paper.Extension.Singleton.emptyIsInitial Seed))
    have := preservesColimitsOfShape_pempty_of_preservesInitial (incl)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (incl) (Fin n)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueCoproducts
