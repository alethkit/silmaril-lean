module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms

/-! # Let-bound state changes and feedback in the Paper singleton category -/

public section

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open CfgEta.TypeCategory (returnRegion returnRegion_branchValue)
open Silmaril.DeBruijn (lift)

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnUniformity

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A D E B : τ} {a b : Tm Φ}

local notation "Comp" => TypeCategory (τ := τ) Φ
local notation "iter" => Paper.TypeCategory.iterate

theorem returnTerm_branchValue (ha : Tm.BranchValue [A] a D) :
    returnTerm ha.hasType = ofRegion (.br (ℓ := 0) rfl ha) :=
  (ofRegion_eq_iff _ _).mpr (.cfgEta (.native (.base (returnRegion_branchValue ha))))

omit [HasTy Φ τ] in
private theorem returnRegion_branchValue_as_let {Γ : VCtx τ} {A : τ} {a : Tm Φ}
    (ha : Tm.BranchValue Γ a A) :
    returnRegion a = .let₁ a (.br 0 (.var 0)) := by
  cases ha <;> rfl

private theorem cut_return_at_variable (q : Region Φ) :
    ((Region.br 0 (.var 0)).lsubst (liftLSubstVars (fun _ => q))) = q := by
  simp only [lsubst, liftLSubstVars, substVars_renameVars]
  have e : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [e, substVars_var]

omit [HasTy Φ τ] in
private theorem branchValue_single {Γ : VCtx τ}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b D) :
    Tm.BranchValue Γ (b.subst (Tm.singleSubst a)) D := by
  have h : ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue Γ (Tm.singleSubst a i) T := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact ha
    | succ i => exact .var (show At Γ i T from hi)
  induction hb with
  | var hi => exact h hi
  | unit => exact .unit
  | pair _ _ il ir => exact .pair il ir
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

/-- A constructor-bound unary let reduces to the substituted constructor
return even when its body uses the original input. -/
theorem constructorReturn_let (ha : Tm.BranchValue [A] a D)
    (hb : Tm.BranchValue [D, A] b E) :
    ConstructorReturn (returnTerm (.let₁ ha.hasType hb.hasType)) := by
  refine ⟨_, branchValue_single ha hb, (ofRegion_eq_iff _ _).2 ?_⟩
  have elt : returnRegion (.let₁ a b) = Region.let₁ a (returnRegion b) := by
    change (returnRegion a).lsubst (fun _ => returnRegion b) = _
    rw [returnRegion_branchValue_as_let ha]
    change Region.let₁ a ((Region.br 0 (.var 0)).lsubst
      (liftLSubstVars (fun _ => returnRegion b))) = _
    rw [cut_return_at_variable]
  rw [elt]
  exact (Paper.Eqv.let₁ ha.hasType (.cfgEta (.native (.base (returnRegion_branchValue hb))))).trans
    (.cfgEta (.native (.letValue ha (.br (ℓ := 0) rfl hb.hasType))))

theorem constructorReturn_id (A : Comp) : ConstructorReturn (𝟙 A) := by
  let a : τ := A
  have h : Tm.BranchValue [a] (.var 0 : Tm Φ) a := .var (i := 0) rfl
  exact ⟨_, h, (returnTerm_id a).symm.trans (returnTerm_branchValue h)⟩

theorem constructorReturn_comp {X Y Z : Comp} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : ConstructorReturn f) (hg : ConstructorReturn g) : ConstructorReturn (f ≫ g) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  let x : τ := X
  let y : τ := Y
  have hw : Tm.BranchValue (y :: x :: []) (b.rename (lift Nat.succ)) (show τ from Z) := by
    have ht : ValueBranches [y] (.br 0 b) [show τ from Z] := .br rfl hb
    have hrename := ht.renameVars ((Ren.wk [] x).lift y)
    cases hrename with
    | br hi hv => cases Option.some.inj hi; exact hv
  rw [← returnTerm_branchValue ha, ← returnTerm_branchValue hb, returnTerm_comp]
  exact constructorReturn_let ha hw

theorem iterate_uniformity_ofConstructorReturn {X Y Z : Comp} {h : X ⟶ Y}
    (hh : ConstructorReturn h) (f : X ⟶ Z ⨿ X) (g : Y ⟶ Z ⨿ Y)
    (comm : f ≫ coprod.map (𝟙 Z) h = h ≫ g) :
    iter f = h ≫ iter g := by
  obtain ⟨a, ha, rfl⟩ := hh
  exact iterate_uniformity_ofBranchValue ha f g comm

theorem iterate_uniformity_ofReturnTerm {X D B : τ} {a c : Tm Φ}
    (ha : Tm.HasType [X] a D) (hc : Tm.BranchValue [X] c D)
    (e : Paper.Eqv [X] (returnRegion a) (.br 0 c) [D])
    (f : ofType (Φ := Φ) X ⟶ ofType B ⨿ ofType X)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (comm : f ≫ coprod.map (𝟙 (ofType B)) (returnTerm ha) = returnTerm ha ≫ g) :
    iter f = returnTerm ha ≫ iter g := by
  exact iterate_uniformity_ofConstructorReturn ⟨c, hc, (ofRegion_eq_iff _ _).mpr e⟩ f g comm



/-- Both injections of this coproduct have constructor-valued representatives.
The coproduct need not be the installed choice. -/
private structure MutualCarrier (X Z : Comp) where
  obj : Comp
  inl : X ⟶ obj
  inr : Z ⟶ obj
  desc {Y : Comp} : (X ⟶ Y) → (Z ⟶ Y) → (obj ⟶ Y)
  inl_desc {Y : Comp} (f : X ⟶ Y) (g : Z ⟶ Y) : inl ≫ desc f g = f
  inr_desc {Y : Comp} (f : X ⟶ Y) (g : Z ⟶ Y) : inr ≫ desc f g = g
  ext {Y : Comp} {f g : obj ⟶ Y} : inl ≫ f = inl ≫ g → inr ≫ f = inr ≫ g → f = g
  inl_constructor : ConstructorReturn inl
  inr_constructor : ConstructorReturn inr

attribute [reassoc (attr := simp)] MutualCarrier.inl_desc MutualCarrier.inr_desc

private def MutualCarrier.swap {X Z : Comp} (S : MutualCarrier X Z) : MutualCarrier Z X where
  obj := S.obj
  inl := S.inr
  inr := S.inl
  desc f g := S.desc g f
  inl_desc f g := S.inr_desc g f
  inr_desc f g := S.inl_desc g f
  ext hl hr := S.ext hr hl
  inl_constructor := S.inr_constructor
  inr_constructor := S.inl_constructor

private noncomputable def MutualCarrier.alternating {X Y Z : Comp} (S : MutualCarrier X Z)
    (g : X ⟶ Y ⨿ Z) (h : Z ⟶ Y ⨿ X) : S.obj ⟶ Y ⨿ S.obj :=
  S.desc (g ≫ coprod.map (𝟙 Y) S.inr) (h ≫ coprod.map (𝟙 Y) S.inl)

private theorem map_as_desc {X Y Z W : Comp} (f : X ⟶ Z) (g : Y ⟶ W) :
    coprod.map f g = coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) := by
  apply coprod.hom_ext <;> simp

-- Eliminate the right state first. Its inner loop stops on that branch.
private theorem alternating_left {X Y Z : Comp} (S : MutualCarrier X Z)
    (g : X ⟶ Y ⨿ Z) (h : Z ⟶ Y ⨿ X) :
    S.inl ≫ iter (S.alternating g h) =
      iter (g ≫ coprod.desc coprod.inl h) := by
  let a : X ⟶ (Y ⨿ S.obj) ⨿ Z := g ≫ coprod.map coprod.inl (𝟙 Z)
  let b : Z ⟶ Y ⨿ S.obj := h ≫ coprod.map (𝟙 Y) S.inl
  let c : Z ⟶ (Y ⨿ S.obj) ⨿ Z := b ≫ coprod.inl
  let inner : S.obj ⟶ (Y ⨿ S.obj) ⨿ S.obj :=
    S.desc (a ≫ coprod.map (𝟙 _) S.inr) (c ≫ coprod.map (𝟙 _) S.inr)
  let r : X ⟶ Y ⨿ X := g ≫ coprod.desc coprod.inl h
  have stop : iter c = b := by
    rw [iterate_fixpoint]
    simp [c]
  have right : S.inr ≫ iter inner = b := by
    rw [← iterate_uniformity_ofConstructorReturn S.inr_constructor c inner (by simp [inner]), stop]
  have left : S.inl ≫ iter inner = r ≫ coprod.map (𝟙 Y) S.inl := by
    calc
      _ = S.inl ≫ (inner ≫ coprod.desc (𝟙 (Y ⨿ S.obj)) (iter inner)) :=
        congrArg (S.inl ≫ ·) (iterate_fixpoint inner)
      _ = a ≫ coprod.desc (𝟙 (Y ⨿ S.obj)) b := by simp [inner, right]
      _ = _ := by simp [a, b, r, map_as_desc, -coprod.desc_comp_inl_comp_inr]
  have merged : inner ≫ coprod.desc (𝟙 (Y ⨿ S.obj)) coprod.inr = S.alternating g h := by
    apply S.ext
    · simp [inner, a, MutualCarrier.alternating, map_as_desc, -coprod.desc_comp_inl_comp_inr]
    · simp [inner, c, b, MutualCarrier.alternating]
  calc
    S.inl ≫ iter (S.alternating g h) =
        S.inl ≫ iter (iter inner) := by rw [iterate_codiagonal, merged]
    _ = iter r := (iterate_uniformity_ofConstructorReturn S.inl_constructor r _ left.symm).symm

-- Eliminate both ways on the same carrier, then unfold the first step.
private theorem dinaturality_of_carrier {X Y Z : Comp} (S : MutualCarrier X Z)
    (g : X ⟶ Y ⨿ Z) (h : Z ⟶ Y ⨿ X) :
    iter (g ≫ coprod.desc coprod.inl h) =
      g ≫ coprod.desc (𝟙 Y) (iter (h ≫ coprod.desc coprod.inl g)) := by
  have same : S.swap.alternating h g = S.alternating g h := rfl
  have right := alternating_left S.swap h g
  rw [same] at right
  change S.inr ≫ iter (S.alternating g h) = _ at right
  rw [← alternating_left S g h, ← right]
  calc
    _ = S.inl ≫ (S.alternating g h ≫ coprod.desc (𝟙 Y) (iter (S.alternating g h))) :=
      congrArg (S.inl ≫ ·) (iterate_fixpoint (S.alternating g h))
    _ = _ := by simp [MutualCarrier.alternating]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sumCarrier (X Z : Comp) : MutualCarrier X Z := by
  let x : τ := X
  let z : τ := Z
  let e := sumCofanIsColimit (Φ := Φ) x z
  refine ⟨(sumCofan x z).pt, (sumCofan x z).inl, (sumCofan x z).inr,
    (fun f g => e.desc (BinaryCofan.mk f g)), ?_, ?_, ?_, ?_, ?_⟩
  · intro Y f g
    exact e.fac (BinaryCofan.mk f g) ⟨.left⟩
  · intro Y f g
    exact e.fac (BinaryCofan.mk f g) ⟨.right⟩
  · intro Y f g hl hr
    exact BinaryCofan.IsColimit.hom_ext e hl hr
  · exact ⟨_, .inl (.var (i := 0) rfl), sumCofan_inl x z⟩
  · exact ⟨_, .inr (.var (i := 0) rfl), sumCofan_inr x z⟩

theorem iterate_dinaturality {X Y Z : Comp}
    (g : X ⟶ Y ⨿ Z) (h : Z ⟶ Y ⨿ X) :
    iter (g ≫ coprod.desc coprod.inl h) =
      g ≫ coprod.desc (𝟙 Y) (iter (h ≫ coprod.desc coprod.inl g)) :=
  dinaturality_of_carrier (sumCarrier X Z) g h

theorem iterate_roll {X Y Z : Comp} (h : X ⟶ Z) (step : Z ⟶ Y ⨿ X) :
    iter (h ≫ step) = h ≫ iter (step ≫ coprod.map (𝟙 Y) h) := by
  have eq := iterate_dinaturality (h ≫ (coprod.inr : Z ⟶ Y ⨿ Z)) step
  simpa [map_as_desc] using eq

/-- An intermediate step that factors both sides suffices to move a
typed state return through iteration. -/
theorem iterate_uniformity_ofFactorization (ha : Tm.HasType [A] a D)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (step : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType A)
    (hf : f = returnTerm ha ≫ step)
    (hg : g = step ≫ coprod.map (𝟙 (ofType B)) (returnTerm ha)) :
    iter f = returnTerm ha ≫ iter g := by
  rw [hf, hg]
  exact iterate_roll (returnTerm ha) step

/-- For a return with an inverse the simulation square determines the
intermediate step. -/
theorem iterate_uniformity_ofReturnIso (ha : Tm.HasType [A] a D)
    (e : ofType (Φ := Φ) A ≅ ofType D) (he : e.hom = returnTerm ha)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (comm : f ≫ coprod.map (𝟙 (ofType B)) (returnTerm ha) = returnTerm ha ≫ g) :
    iter f = returnTerm ha ≫ iter g := by
  apply iterate_uniformity_ofFactorization ha f g (e.inv ≫ f)
  · rw [← he, Iso.hom_inv_id_assoc]
  · rw [Category.assoc, comm, ← he, Iso.inv_hom_id_assoc]

local notation "U" => (ofType (Φ := Φ) (Silmaril.unit : τ))

private theorem iterate_repeat_eq_discard {X Y : Comp} (h : X ⟶ X)
    (keepDiscard : PreservesDiscard h) :
    iterate (h ≫ (coprod.inr : X ⟶ Y ⨿ X)) =
      discardArrow (show τ from X) ≫ iterate (coprod.inr : U ⟶ Y ⨿ U) := by
  let d := discardArrow (Φ := Φ) (show τ from X)
  have dValue : ConstructorReturn d := ⟨.unit, .unit, rfl⟩
  apply iterate_uniformity_ofConstructorReturn dValue
  change (h ≫ coprod.inr) ≫ coprod.map (𝟙 Y) d = d ≫ coprod.inr
  change h ≫ d = d at keepDiscard
  rw [Category.assoc, coprod.inr_map, ← Category.assoc, keepDiscard]

theorem iterate_double_of_preservesDiscard {X Y : Comp} (h : X ⟶ X)
    (keepDiscard : PreservesDiscard h) :
    let g := h ≫ (coprod.inr : X ⟶ Y ⨿ X)
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g := by
  dsimp only
  rw [Category.assoc, coprod.inr_desc, ← Category.assoc h h,
    iterate_repeat_eq_discard (h ≫ h) ((PreservesDiscard (τ := τ) (Φ := Φ)).comp_mem _ _ keepDiscard keepDiscard),
    iterate_repeat_eq_discard h keepDiscard]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnUniformity
