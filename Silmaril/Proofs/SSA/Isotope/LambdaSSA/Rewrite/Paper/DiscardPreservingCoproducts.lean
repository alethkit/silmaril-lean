module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Case.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Shuffle.SharedInput.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Thms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! # Coproducts of discard-preserving values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCoproducts

open CategoryTheory CategoryTheory.Limits
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.TypeCategory (ofType ofRegion emptyHom_ext exists_ofRegion ofRegion_eq_iff
  returnTerm CentralCopies pairArrows diagonalArrow
  sumCofan sumIso sumCofan_inl sumCofan_inr sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom
  sumCofan_inl_sumIso_hom_assoc sumCofan_inr_sumIso_hom_assoc
  sumCofanIsColimit whiskerCentral_ofRegion_branchValue pairArrows_copy_branchValue pairArrows_comp_common)
open CfgEta.TypeCategory (returnRegion_typed)
open Silmaril.DeBruijn (lift)

universe u v w
open Paper.Extension.Singleton (TypeCategory projection DiscardPreservingReturn DiscardPreservingValueCategory
  ProjectedPureReturn projected_branchValue_mem)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair CopairPure CaseReturnAgreement)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
local notation "Comp" => Paper.TypeCategory (τ := τ) Φ
local notation "U" => (Silmaril.empty : τ)

set_option backward.isDefEq.respectTransparency false in
private theorem product_hom_ext_of_empty {A B : τ} {Y : Comp} {i : Nat}
    (hi : At [B, A, product A B] i U) (f g : ofType (product A B) ⟶ Y) : f = g := by
  obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
  obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
  apply (ofRegion_eq_iff _ _).2
  apply (Paper.product_variable_eta_iff (i := 0) (rfl : At [product A B] 0 (product A B))
    hf.hasType hg.hasType).1
  have hs : Tm.Subst.HasType [product A B] [B, A, product A B] (Paper.splitProduct (Φ := Φ) 0) := by
    intro j D hj
    cases j with
    | zero => cases Option.some.inj hj; exact .pair (.var rfl) (.var rfl)
    | succ j => simp [At] at hj
  exact .cfgEta (.native (.initial (.var hi) (hf.hasType.substVars hs) (hg.hasType.substVars hs)))

set_option backward.isDefEq.respectTransparency false in
private theorem empty_copies {B : Comp} (f : ofType U ⟶ B) : CentralCopies f := by
  constructor
  · intro X Y g
    exact ⟨product_hom_ext_of_empty (i := 1) rfl _ _, product_hom_ext_of_empty (i := 0) rfl _ _⟩
  · exact emptyHom_ext _ _

private noncomputable abbrev copair {A B D : τ} (f : ofType (Φ := Φ) A ⟶ ofType D) (g : ofType (Φ := Φ) B ⟶ ofType D) :=
  (sumIso A B).hom ≫ coprod.desc f g

@[reassoc] private theorem copair_inl {A B D : τ} (f : ofType (Φ := Φ) A ⟶ ofType D)
    (g : ofType (Φ := Φ) B ⟶ ofType D) : (sumCofan A B).inl ≫ copair f g = f :=
  (Category.assoc _ _ _).symm.trans ((sumCofan_inl_sumIso_hom_assoc A B _).trans (coprod.inl_desc _ _))

@[reassoc] private theorem copair_inr {A B D : τ} (f : ofType (Φ := Φ) A ⟶ ofType D)
    (g : ofType (Φ := Φ) B ⟶ ofType D) : (sumCofan A B).inr ≫ copair f g = g :=
  (Category.assoc _ _ _).symm.trans ((sumCofan_inr_sumIso_hom_assoc A B _).trans (coprod.inr_desc _ _))

private theorem inl_copies (A B : τ) : CentralCopies (sumCofan (Φ := Φ) A B).inl := by
  rw [sumCofan_inl]
  exact ⟨whiskerCentral_ofRegion_branchValue (.inl (.var rfl)), pairArrows_copy_branchValue (.inl (.var rfl))⟩

private theorem inr_copies (A B : τ) : CentralCopies (sumCofan (Φ := Φ) A B).inr := by
  rw [sumCofan_inr]
  exact ⟨whiskerCentral_ofRegion_branchValue (.inr (.var rfl)), pairArrows_copy_branchValue (.inr (.var rfl))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem copair_copies {A B D : τ} {f : ofType (Φ := Φ) A ⟶ ofType D}
    {g : ofType (Φ := Φ) B ⟶ ofType D} (hf : CentralCopies f) (hg : CentralCopies g) :
    CentralCopies (copair f g) := by
  refine ⟨Paper.TypeCategory.whiskerCentral_sumCofan_desc f g hf.1 hg.1, ?_⟩
  change pairArrows (copair f g) (copair f g) = copair f g ≫ diagonalArrow D
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit A B)
  · have h := pairArrows_comp_common _ (copair f g) (copair f g) (inl_copies A B)
    rw [copair_inl] at h
    rw [← Category.assoc, copair_inl]
    exact h.symm.trans hf.2
  · have h := pairArrows_comp_common _ (copair f g) (copair f g) (inr_copies A B)
    rw [copair_inr] at h
    rw [← Category.assoc, copair_inr]
    exact h.symm.trans hg.2


variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop) (pe : ε)

set_option hygiene false in
local notation "Q" => TypeCategory Seed
set_option hygiene false in
local notation "F" => projection Seed
set_option hygiene false in
local notation "V" => DiscardPreservingValueCategory Seed pe
set_option hygiene false in
local notation "J" => wideSubcategoryInclusion (DiscardPreservingReturn Seed pe)
set_option hygiene false in
local notation "Obj" => Paper.Extension.Singleton.ofType (Φ := Φ) Seed
local notation "U" => (Silmaril.empty : τ)
set_option hygiene false in
local notation "cf" => Paper.Extension.Singleton.sumCofan Seed
set_option hygiene false in
local notation "cfLim" => Paper.Extension.Singleton.sumCofanIsColimit Seed

set_option backward.isDefEq.respectTransparency false in
theorem empty_mem {Y : Q} (f : Obj U ⟶ Y) : DiscardPreservingReturn Seed pe f := by
  obtain ⟨g, rfl⟩ := (F).map_surjective (Y := Y.as) f
  have pure : Paper.TypeCategory.PureReturn pe g := by
    let ht : Tm.HasType [U] (.abort (.var 0) : Tm Φ) (show τ from Y.as) := .abort (.var rfl)
    exact ⟨_, ht, .abort .var, emptyHom_ext _ _⟩
  refine ⟨⟨⟨g, pure, rfl⟩, ⟨g, empty_copies g, rfl⟩⟩, ?_⟩
  exact (Paper.Extension.Singleton.emptyIsInitial Seed).hom_ext _ _

noncomputable def valueEmptyIsInitial : IsInitial (⟨Obj U⟩ : V) :=
  IsInitial.ofUniqueHom
    (fun Y => ⟨(Paper.Extension.Singleton.emptyIsInitial Seed).to Y.obj, empty_mem Seed pe _⟩)
    (fun _ _ => (J).map_injective ((Paper.Extension.Singleton.emptyIsInitial Seed).hom_ext _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem inl_mem (A B : τ) : DiscardPreservingReturn Seed pe (cf A B).inl := by
  change DiscardPreservingReturn Seed pe ((F).map (sumCofan A B).inl)
  rw [sumCofan_inl]
  have ha : Tm.BranchValue [A] (.inl (.var 0) : Tm Φ) (Silmaril.coprod A B) := .inl (.var rfl)
  exact ⟨projected_branchValue_mem Seed pe ha,
    (Functor.map_comp (F) _ _).symm.trans (congrArg (F).map (Paper.TypeCategory.discard_comp_branchValue ha))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem inr_mem (A B : τ) : DiscardPreservingReturn Seed pe (cf A B).inr := by
  change DiscardPreservingReturn Seed pe ((F).map (sumCofan A B).inr)
  rw [sumCofan_inr]
  have ha : Tm.BranchValue [B] (.inr (.var 0) : Tm Φ) (Silmaril.coprod A B) := .inr (.var rfl)
  exact ⟨projected_branchValue_mem Seed pe ha,
    (Functor.map_comp (F) _ _).symm.trans (congrArg (F).map (Paper.TypeCategory.discard_comp_branchValue ha))⟩

@[reassoc] theorem exactCopair_inl {A B : τ} {D : Q} (f : Obj A ⟶ D) (g : Obj B ⟶ D) :
    (cf A B).inl ≫ exactCopair Seed f g = f := (cfLim A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[reassoc] theorem exactCopair_inr {A B : τ} {D : Q} (f : Obj A ⟶ D) (g : Obj B ⟶ D) :
    (cf A B).inr ≫ exactCopair Seed f g = g := (cfLim A B).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency false in
private theorem map_copair {A B D : τ} (f : ofType (Φ := Φ) A ⟶ ofType D) (g : ofType (Φ := Φ) B ⟶ ofType D) :
    (F).map (copair f g) = exactCopair Seed ((F).map f) ((F).map g) := by
  apply BinaryCofan.IsColimit.hom_ext (cfLim A B)
  · rw [exactCopair_inl]
    change (F).map (sumCofan A B).inl ≫ (F).map (copair f g) = _
    rw [← Functor.map_comp, copair_inl]
  · rw [exactCopair_inr]
    change (F).map (sumCofan A B).inr ≫ (F).map (copair f g) = _
    rw [← Functor.map_comp, copair_inr]

set_option backward.isDefEq.respectTransparency false in
theorem exactCopair_mem_iff {A B : τ} {D : Q} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : DiscardPreservingReturn Seed pe f) (hg : DiscardPreservingReturn Seed pe g) :
    DiscardPreservingReturn Seed pe (exactCopair Seed f g) ↔
      ProjectedPureReturn Seed pe (exactCopair Seed f g) := by
  refine ⟨fun h => h.1.1, fun hp => ⟨⟨hp, ?_⟩, ?_⟩⟩
  · obtain ⟨f₀, hf₀, rfl⟩ := hf.1.2
    obtain ⟨g₀, hg₀, rfl⟩ := hg.1.2
    exact ⟨_, copair_copies hf₀ hg₀, map_copair Seed f₀ g₀⟩
  · apply BinaryCofan.IsColimit.hom_ext (cfLim A B)
    · rw [← Category.assoc, exactCopair_inl, hf.2]
      exact (inl_mem Seed pe A B).2.symm
    · rw [← Category.assoc, exactCopair_inr, hg.2]
      exact (inr_mem Seed pe A B).2.symm

def valueSumCofan (A B : τ) :
    BinaryCofan (⟨Obj A⟩ : V) (⟨Obj B⟩ : V) :=
  BinaryCofan.mk (P := (⟨Obj (Silmaril.coprod A B)⟩ : V))
    ⟨(cf A B).inl, inl_mem Seed pe A B⟩ ⟨(cf A B).inr, inr_mem Seed pe A B⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def valueSumIsColimit (h : CopairPure Seed pe) (A B : τ) :
    IsColimit (valueSumCofan Seed pe A B) :=
  BinaryCofan.IsColimit.mk (valueSumCofan Seed pe A B)
    (fun f g => ⟨exactCopair Seed f.1 g.1, (exactCopair_mem_iff Seed pe f.2 g.2).2 (h f.2 g.2)⟩)
    (fun {_} f g => by
      apply (J).map_injective
      exact exactCopair_inl Seed f.1 g.1)
    (fun {_} f g => by
      apply (J).map_injective
      exact exactCopair_inr Seed f.1 g.1)
    (fun {_} f g _ hl hr => (J).map_injective ((BinaryCofan.IsColimit.hom_ext (cfLim A B))
      ((congrArg (J).map hl).trans (exactCopair_inl Seed f.1 g.1).symm)
      ((congrArg (J).map hr).trans (exactCopair_inr Seed f.1 g.1).symm)))

theorem valueHasFiniteCoproducts (h : CopairPure Seed pe) : HasFiniteCoproducts V :=
  haveI : HasInitial V := (valueEmptyIsInitial Seed pe).hasInitial
  haveI : HasBinaryCoproducts V :=
    haveI (X Y : V) : HasBinaryCoproduct X Y :=
      ⟨⟨⟨_, valueSumIsColimit Seed pe h (show τ from X.obj.as) (show τ from Y.obj.as)⟩⟩⟩
    hasBinaryCoproducts_of_hasColimit_pair _
  hasFiniteCoproducts_of_has_binary_and_initial

theorem valuePreservesInitial : PreservesColimit (Functor.empty.{0} V) (J) :=
  preservesColimit_of_preserves_colimit_cocone (valueEmptyIsInitial Seed pe)
    ((isColimitMapCoconeEmptyCoconeEquiv (J) _).symm (Paper.Extension.Singleton.emptyIsInitial Seed))

set_option backward.isDefEq.respectTransparency false in
theorem valuePreservesFiniteCoproducts (h : CopairPure Seed pe) : PreservesFiniteCoproducts (J) where
  preserves n := by
    let := valueHasFiniteCoproducts Seed pe h
    have : PreservesColimitsOfShape (Discrete WalkingPair) (J) :=
      { preservesColimit := fun {K} => by
          let A : τ := (K.obj ⟨WalkingPair.left⟩).obj.as
          let B : τ := (K.obj ⟨WalkingPair.right⟩).obj.as
          have hm : IsColimit (BinaryCofan.map (J) (valueSumCofan Seed pe A B)) := by
            change IsColimit (cf A B)
            exact cfLim A B
          have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) (J) :=
            preservesColimit_of_preserves_colimit_cocone
              (valueSumIsColimit Seed pe h A B) (BinaryCofan.isColimitMapCoconeEquiv.symm hm)
          exact preservesColimit_of_iso_diagram (J) (diagramIsoPair K).symm }
    have := valuePreservesInitial Seed pe
    have := preservesColimitsOfShape_pempty_of_preservesInitial (J)
    exact PreservesFiniteCoproducts.of_preserves_binary_and_initial (J) (Fin n)


set_option backward.isDefEq.respectTransparency false in
theorem copairPure_of_caseReturn (h : CaseReturnAgreement Seed pe) : CopairPure Seed pe := by
  intro A B D f g hf hg
  obtain ⟨f₀, ⟨a, ha, pa, rfl⟩, rfl⟩ := hf.1.1
  obtain ⟨g₀, ⟨b, hb, pb, rfl⟩, rfl⟩ := hg.1.1
  let S := Silmaril.coprod A B
  have ht : Tm.HasType [S]
      (.case (.var 0) (a.rename (lift Nat.succ)) (b.rename (lift Nat.succ))) (show τ from D.as) :=
    .case (.var rfl) (ha.rename ((Ren.wk [] S).lift A)) (hb.rename ((Ren.wk [] S).lift B))
  refine ⟨returnTerm (τ := τ) ht, ⟨_, ht, .case .var (pa.rename _) (pb.rename _), rfl⟩, ?_⟩
  rw [← map_copair Seed]
  refine Eq.trans ?_ (congrArg (projection Seed).map
    (Paper.TypeCategory.coprod_desc_ofRegion (returnRegion_typed ha) (returnRegion_typed hb)).symm)
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2 (h ha hb pa pb)

theorem copairPure_iff_valueSums : CopairPure Seed pe ↔
    ∀ A B : τ, Nonempty (IsColimit (valueSumCofan Seed pe A B)) := by
  refine ⟨fun h A B => ⟨valueSumIsColimit Seed pe h A B⟩, ?_⟩
  intro h A B D f g hf hg
  obtain ⟨hc⟩ := h A B
  let legs : BinaryCofan (⟨Paper.Extension.Singleton.ofType Seed A⟩ : DiscardPreservingValueCategory Seed pe) ⟨Paper.Extension.Singleton.ofType Seed B⟩ :=
    BinaryCofan.mk (P := ⟨D⟩) ⟨f, hf⟩ ⟨g, hg⟩
  let d := hc.desc legs
  have e : d.hom = exactCopair Seed f g := by
    apply BinaryCofan.IsColimit.hom_ext (Paper.Extension.Singleton.sumCofanIsColimit Seed A B)
    · exact (congrArg
        (fun k => (wideSubcategoryInclusion (DiscardPreservingReturn Seed pe)).map k)
        (hc.fac legs ⟨WalkingPair.left⟩)).trans (exactCopair_inl Seed f g).symm
    · exact (congrArg
        (fun k => (wideSubcategoryInclusion (DiscardPreservingReturn Seed pe)).map k)
        (hc.fac legs ⟨WalkingPair.right⟩)).trans (exactCopair_inr Seed f g).symm
  exact e ▸ d.property.1.1

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.DiscardPreservingCoproducts
