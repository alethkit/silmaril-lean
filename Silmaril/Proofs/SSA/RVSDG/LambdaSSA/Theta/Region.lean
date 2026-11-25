module

public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Combinators

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory (snd lift)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA (Tm Region)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop splitMapCoprod)

universe u v d h c k
variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D] [HasFiniteCoproducts D]
variable (M : TypeModel τ D) {A : τ}

set_option backward.isDefEq.respectTransparency false

private abbrev R (A : τ) : Fin 1 → τ := fun _ => A
private noncomputable def outward (A : τ) : M.obj A ⟶ labelObj M [A] :=
  labelInject M 0 rfl
private noncomputable def localLabel (A : τ) : M.obj A ⟶ labelObj M [A, A] :=
  labelInject M 0 rfl
private noncomputable def exitLabel (A : τ) : M.obj A ⟶ labelObj M [A, A] :=
  labelInject M 1 rfl

private noncomputable def finiteOut (A : τ) : finiteLabelObj M (R A) ⟶ M.obj A :=
  Sigma.desc (fun _ => 𝟙 (M.obj A))

private noncomputable def localOut (A : τ) : labelObj M [A] ⟶ M.obj A :=
  labelObjToFinite M (R A) ≫ finiteOut M A

private theorem out_in (A : τ) : outward M A ≫ localOut M A = 𝟙 (M.obj A) := by
  unfold outward localOut labelInject labelObjToFinite finiteOut finiteLabelInject
  simp only [eqToHom_refl, Category.id_comp]
  rw [Sigma.ι_comp_desc_assoc]
  simp

private theorem split_local (A : τ) :
    localLabel M A ≫ labelAppendSplit M [A] [A] = outward M A ≫ coprod.inr := by
  unfold localLabel labelInject labelAppendSplit
  simp [labelAppendRoute, outward, labelInject]

private theorem split_exit (A : τ) :
    exitLabel M A ≫ labelAppendSplit M [A] [A] = outward M A ≫ coprod.inl := by
  unfold exitLabel labelInject labelAppendSplit
  simp [labelAppendRoute, outward, labelInject]

variable {C : Type c} [Category.{k} C] [SymmetricCategory D]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor D] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : D ⥤ C) [StrongElgotFreydCategory J] [InstructionModel J M Φ]

variable (prim : ∀ f : Φ, M.obj (instrSrc f) ⟶ M.obj (instrTrg f))
variable (agrees : ∀ f : Φ, InstructionModel.denote (J := J) (M := M) f = J.map (prim f))

include agrees

private theorem op_denotes (op : Φ) (Γ : List τ) (A B : τ)
    (source : instrSrc op = A) (target : instrTrg op = B)
    (h : Tm.HasType (A :: Γ) (.op op (.var 0)) B) :
    Denotes J M h (J.map (snd (ctxObj M Γ) (M.obj A) ≫
      eqToHom (congrArg M.obj source.symm) ≫ prim op ≫ eqToHom (congrArg M.obj target))) := by
  subst A
  subst B
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [J.map_comp, ← agrees]
  exact .op (.var rfl)

private theorem block_denotes (s : Step Φ A) :
    RegionDenotes J M (blockTyping s)
      (J.map (snd (ctxObj M [A]) (M.obj A) ≫
        stepMap M prim s ≫ coprod.desc (exitLabel M A) (localLabel M A))) := by
  let E := ctxObj M [A]
  let X := M.obj A
  have ds := op_denotes M J prim agrees s.op [A] A (Silmaril.coprod A A)
    s.input s.output (s.typing [A])
  have dl : RegionDenotes J M
      (.br (L := [A, A]) (ℓ := 1) rfl (.var (Φ := Φ) (Γ := [A, A, A]) (i := 0) rfl))
        (J.map (snd (E ⊗ X) X ≫ exitLabel M A)) := by
    rw [J.map_comp]
    exact .br (.var rfl)
  have dr : RegionDenotes J M
      (.br (L := [A, A]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A, A, A]) (i := 0) rfl))
        (J.map (snd (E ⊗ X) X ≫ localLabel M A)) := by
    rw [J.map_comp]
    exact .br (.var rfl)
  have den := RegionDenotes.case ds dl dr
  simp only [← J.map_comp, Category.assoc] at den
  change RegionDenotes J M (blockTyping s)
    (caseWithContext J (J.map (snd E X ≫ stepMap M prim s))
      (J.map (snd (E ⊗ X) X ≫ exitLabel M A))
      (J.map (snd (E ⊗ X) X ≫ localLabel M A))) at den
  have cases := case_project J (snd E X ≫ stepMap M prim s)
    (exitLabel M A) (localLabel M A)
  rw [cases, Category.assoc] at den
  exact den

theorem region_iterates (s : Step Φ A) :
    RegionDenotes J M (regionTyping s)
      (J.map (snd (𝟙_ D) (M.obj A)) ≫
        iterate (J.map (stepMap M prim s) ≫ splitMapCoprod J (M.obj A) (M.obj A)) ≫
        J.map (labelInject M (L := [A]) 0 rfl)) := by
  let E := ctxObj M [A]
  let X := M.obj A
  let L := labelObj M [A]
  let i := outward M A
  let p := localOut M A
  let f := stepMap M prim s
  let fBlock := snd E X ≫ f ≫ coprod.desc (exitLabel M A) (localLabel M A)
  let col := J.map ((E ◁ finiteOut M A) ≫ fBlock)
  have collect : CollectiveDenotes J M [A] (R A) [A] (fun _ => J.map fBlock) col := by
    constructor
    intro j
    change J.map ((𝟙 E) ⊗ₘ finiteLabelInject M (R A) j) ≫
      J.map ((E ◁ finiteOut M A) ≫ fBlock) = J.map fBlock
    simp [← J.map_comp_assoc, finiteLabelInject, finiteOut, ← MonoidalCategory.whiskerLeft_comp]
  have entry : RegionDenotes J M
      (.br (L := [A, A]) (ℓ := 0) rfl (.var (Φ := Φ) (Γ := [A]) (i := 0) rfl))
      (J.map (snd (𝟙_ D) X ≫ localLabel M A)) := by
    rw [J.map_comp]
    exact .br (.var rfl)
  have cfg := RegionDenotes.cfg _ _ entry (fun _ => block_denotes M J prim agrees s) collect
  have init : J.map (snd (𝟙_ D) X ≫ localLabel M A) ≫
      J.map (labelAppendSplit M [A] [A]) =
      J.map ((snd (𝟙_ D) X ≫ i) ≫ (coprod.inr : L ⟶ L ⨿ L)) := by
    rw [← J.map_comp, Category.assoc, split_local, ← Category.assoc]
  have dispatched : J.map ((𝟙 E) ⊗ₘ labelObjToFinite M (R A)) ≫ col ≫
      J.map (labelAppendSplit M [A] [A]) =
      J.map (snd E L ≫ (p ≫ f ≫ coprod.map i i)) := by
    dsimp only [col, fBlock]
    simp only [← J.map_comp, MonoidalCategory.id_tensorHom, Category.assoc]
    rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc,
      CartesianMonoidalCategory.whiskerLeft_snd_assoc]
    rw [coprod.desc_comp, split_exit, split_local]
    change J.map (snd E L ≫ labelObjToFinite M (R A) ≫ finiteOut M A ≫ f ≫
      coprod.desc (i ≫ coprod.inl) (i ≫ coprod.inr)) = _
    have route : coprod.desc (i ≫ coprod.inl) (i ≫ coprod.inr) = coprod.map i i := by
      apply coprod.hom_ext <;> simp
    rw [route]
    simp only [p, localOut, Category.assoc]
  change RegionDenotes J M (regionTyping s) (caseWithContext J
    (J.map (snd (𝟙_ D) X ≫ localLabel M A) ≫ J.map (labelAppendSplit M [A] [A]))
    (J.map (snd E L))
    (contextualLoop J (J.map ((𝟙 E) ⊗ₘ labelObjToFinite M (R A)) ≫ col ≫
      J.map (labelAppendSplit M [A] [A])))) at cfg
  rw [init, dispatched, case_right J, contextual_project J,
    ← J.map_comp_assoc, CartesianMonoidalCategory.lift_snd, J.map_comp, Category.assoc] at cfg
  let source := J.map f ≫ splitMapCoprod J X X
  let target := J.map (p ≫ f ≫ coprod.map i i) ≫ splitMapCoprod J L L
  have square : (source ≫ coprod.map (J.map i) (𝟙 (J.obj X))) ≫
      coprod.map (𝟙 (J.obj L)) (J.map i) = J.map i ≫ target := by
    dsimp only [source, target]
    simp only [Category.assoc, coprod.map_map, Category.id_comp]
    rw [Category.comp_id]
    rw [map_split J, ← J.map_comp_assoc, ← J.map_comp_assoc, ← Category.assoc i p, out_in,
      Category.id_comp]
  have norm : J.map i ≫ iterate target = iterate source ≫ J.map i := by
    rw [ElgotCategory.naturality]
    exact (ElgotFreydCategory.pure_uniformity J _ _ i square).symm
  change RegionDenotes J M (regionTyping s)
    (J.map (snd (𝟙_ D) X) ≫ J.map i ≫ iterate target) at cfg
  rwa [norm] at cfg

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Proofs
