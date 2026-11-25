module

public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Model.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Specializing the categorical diamond without changing primitive models -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Proofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ splitMapCoprod_coprodIsoSum)
open Isotope.LambdaSSA.Semantics
open Isotope.LambdaSSA.Semantics.Monadic (Env LabelDen CategoricalLabelDen LabelValue)
open Isotope.LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel
  RegionTypingCoherent)
open Silmaril.Elgot (Iterate iter LawfulElgotMonad mapReturn)
open LinearChain.Categorical (call choice)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [InstructionModel Φ τ ε m]
variable {A B X Y K E D : τ}

local notation "J" => typeJ (m := m)
local notation "T" => ofMonadicTypeModel (τ := τ)
local notation "encodeLabel" => LabelValue.categoricalEquiv (τ := τ)
local notation "S" => Isotope.LambdaSSA.Semantics.Categorical.labelInject

local notation "instructions" => ofMonadicInstructionModel (τ := τ) (Φ := Φ) (ε := ε) (m := m)

private noncomputable def readChoice (U V : Type u) :
    (J).obj U ⨿ (J).obj V ⟶ (J).obj (U ⊕ V) :=
  (Kleisli.Type.coprodIsoSum m ((J).obj U) ((J).obj V)).hom

private theorem comp_apply {U V W : Type u}
    (f : (J).obj U ⟶ (J).obj V) (g : (J).obj V ⟶ (J).obj W) (a : U) :
    (f ≫ g).of a = (f.of a >>= g.of : m W) :=
  congrFun (Kleisli.Type.comp_of_eq_kleisliRight m f g) a

private theorem map_apply {U V : Type u} (f : U ⟶ V) (a : U) :
    ((J).map f).of a = (pure (f a) : m V) := rfl

private theorem call_apply (p : TwoBlock.Instruction Φ A B) (a : TyDen A) :
    let _ := instructions
    (call J T p).of a = TwoBlock.call (ε := ε) (m := m) p a := by
  intro _
  obtain ⟨op, src, dst⟩ := p
  subst A
  subst B
  simp [call, TwoBlock.call]
  rfl

private theorem choice_apply (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y)) (a : TyDen A) :
    let _ := instructions
    (choice J T p ≫ readChoice (TyDen X) (TyDen Y)).of a = callCase (ε := ε) (m := m) p a := by
  intro _
  let U := (T).obj X
  let V := (T).obj Y
  change (choice J T p ≫ readChoice U V).of a = _
  unfold choice readChoice
  simp only [Category.assoc]
  rw [splitMapCoprod_coprodIsoSum (m := m) U V, ← (J).map_comp, comp_apply, call_apply]
  unfold callCase
  congr 1
  funext x
  rw [map_apply]
  congr 1
  exact Agreement.coprod_hom_agrees X Y x

private theorem branch_apply {O : Type u} (p : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
    (l : (J).obj (TyDen X) ⟶ (J).obj O) (r : (J).obj (TyDen Y) ⟶ (J).obj O) (a : TyDen A) :
    let _ := instructions
    (choice J T p ≫ coprod.desc l r).of a =
      (callCase (ε := ε) (m := m) p a >>= Sum.elim l.of r.of) := by
  intro _
  rw [← Kleisli.Type.coprodIsoSum_hom_sumElim, ← Category.assoc, comp_apply]
  change (show m (TyDen X ⊕ TyDen Y) from
    (choice J T p ≫ readChoice (TyDen X) (TyDen Y)).of a) >>= Sum.elim l.of r.of = _
  rw [choice_apply]

private theorem diamond_apply (s : Branches Φ B X Y K) (b : TyDen B) :
    let _ := instructions
    (Categorical.diamond J T s).of b =
      (callCase (ε := ε) (m := m) s.classifier b >>= runArm (ε := ε) s) := by
  intro _
  unfold Categorical.diamond
  rw [branch_apply]
  congr 1
  funext result
  cases result with
  | inl x => exact call_apply s.left x
  | inr y => exact call_apply s.right y

private theorem body_apply (s : Blocks Φ A B X Y K E D) (b : TyDen B) :
    let _ := instructions
    ((Categorical.diamond J T s.diamond ≫ choice J T s.join) ≫
      readChoice (TyDen D) (TyDen A)).of b = bodyAction (ε := ε) (m := m) s b := by
  intro _
  simp only [Category.assoc, comp_apply (Categorical.diamond J T s.diamond), diamond_apply,
    bodyAction, bind_assoc]
  congr 1
  funext result
  congr 1
  funext k
  exact choice_apply s.join k

@[reassoc] private theorem read_inl (U V : Type u) :
    (coprod.inl : (J).obj U ⟶ (J).obj U ⨿ (J).obj V) ≫ readChoice U V =
      (J).map (TypeCat.ofHom Sum.inl) := by
  rw [readChoice, Kleisli.Type.inl_coprodIsoSum_hom]
  rfl

@[reassoc] private theorem read_inr (U V : Type u) :
    (coprod.inr : (J).obj V ⟶ (J).obj U ⨿ (J).obj V) ≫ readChoice U V =
      (J).map (TypeCat.ofHom Sum.inr) := by
  rw [readChoice, Kleisli.Type.inr_coprodIsoSum_hom]
  rfl

private theorem map_read {U V W : Type u} (f : U ⟶ W) :
    coprod.map ((J).map f) (𝟙 ((J).obj V)) ≫ readChoice W V =
      readChoice U V ≫ (J).map (TypeCat.ofHom (Sum.map f id)) := by
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, read_inl_assoc, read_inl, ← CategoryTheory.Functor.map_comp]
    rfl
  · simp only [coprod.inr_map_assoc, Category.id_comp, read_inr_assoc, read_inr,
      ← CategoryTheory.Functor.map_comp]
    rfl

private theorem label_left (e : TyDen E) :
    S T (L := [E,D]) 0 rfl e = encodeLabel [E,D] (.inl e) := by
  rw [← Monadic.categoricalEquiv_labelInject (L := [E,D]) 0 rfl e,
    Monadic.labelInject_eq_recursive]
  rfl

private theorem label_right (d : TyDen D) :
    S T (L := [E,D]) 1 rfl d = encodeLabel [E,D] (.inr (.inl d)) := by
  rw [← Monadic.categoricalEquiv_labelInject (L := [E,D]) 1 rfl d,
    Monadic.labelInject_eq_recursive]
  rfl

private theorem activation_apply (s : Blocks Φ A B X Y K E D) (a : TyDen A) :
    let _ := instructions
    (Categorical.activation J T s ≫ readChoice (CategoricalLabelDen [E,D]) (TyDen A)).of a =
      (round (ε := ε) (m := m) s a >>= fun r => pure (Sum.map (encodeLabel [E,D]) id r)) := by
  intro _
  let L := CategoricalLabelDen [E,D]
  let left : TyDen E ⟶ L := S T (L := [E,D]) 0 rfl
  let right : TyDen D ⟶ L := S T (L := [E,D]) 1 rfl
  unfold Categorical.activation
  rw [Category.assoc, coprod.desc_comp, branch_apply, round, bind_assoc]
  congr 1
  funext header
  cases header with
  | inl e =>
    change (((J).map left ≫ coprod.inl) ≫ readChoice L (TyDen A)).of e = _
    rw [Category.assoc, read_inl, ← CategoryTheory.Functor.map_comp, map_apply, pure_bind]
    change (pure (Sum.inl (left e)) : m (L ⊕ TyDen A)) = _
    rw [show left e = encodeLabel [E,D] (.inl e) from label_left e]
    rfl
  | inr b =>
    change ((Categorical.diamond J T s.diamond ≫ choice J T s.join ≫
        coprod.map ((J).map right) (𝟙 ((J).obj (TyDen A)))) ≫ readChoice L (TyDen A)).of b = _
    rw [Category.assoc, Category.assoc, map_read, ← Category.assoc, ← Category.assoc, comp_apply]
    change ((show m (TyDen D ⊕ TyDen A) from
      ((Categorical.diamond J T s.diamond ≫ choice J T s.join) ≫ readChoice (TyDen D) (TyDen A)).of b) >>=
        fun r => (pure (Sum.map right id r) : m (L ⊕ TyDen A))) = _
    rw [body_apply, bind_assoc]
    congr 1
    funext result
    cases result with
    | inl d =>
      rw [pure_bind]
      change (pure (Sum.inl (right d)) : m (L ⊕ TyDen A)) = _
      rw [show right d = encodeLabel [E,D] (.inr (.inl d)) from label_right d]
      rfl
    | inr a => rw [pure_bind]; rfl

variable [Iterate m] [LawfulElgotMonad m]

/-- The actual LambdaSSA state computation equals the folded activation loop.
The categorical comparison uses the repository's canonical exit equivalence. -/
theorem region_round_eq (s : Blocks Φ A B X Y K E D)
    (coherent : Agreement.RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := m)) (env : Env [A]) :
    Monadic.Region.denote (ε := ε) (m := m) (regionTyping s) env =
      iter (round (ε := ε) (m := m) s) env.2 := by
  let _ := instructions
  let _ : RegionTypingCoherent (Φ := Φ) J T := coherent
  have h := Agreement.categoricalRegionDenote_eq coherent (regionTyping s) env
  rw [Agreement.categoricalRegionDenote, Categorical.denoteRegion_eq J T s] at h
  have ev : (Categorical.denoteForm J T (Form.loop s)).of (Agreement.envToCategorical env) =
      (iter (round (ε := ε) (m := m) s) env.2 >>= fun label => pure (encodeLabel [E,D] label)) := by
    unfold Categorical.denoteForm Categorical.denote
    rw [comp_apply]
    change ((pure env.2 : m (TyDen A)) >>= _) = _
    rw [pure_bind]
    have activation : (fun a => (Categorical.activation J T s ≫
        readChoice (CategoricalLabelDen [E,D]) (TyDen A)).of a) =
        mapReturn (round (ε := ε) (m := m) s) (fun label => pure (encodeLabel [E,D] label)) := by
      funext a
      rw [activation_apply]
      unfold mapReturn
      congr 1
      funext result
      cases result <;> simp
    change iter (m := m) (fun a : TyDen A => (Categorical.activation J T s ≫
      readChoice (CategoricalLabelDen [E,D]) (TyDen A)).of a) env.2 = _
    exact (congrArg (fun step : TyDen A → m (CategoricalLabelDen [E,D] ⊕ TyDen A) =>
      iter step env.2) activation).trans
      ((congrFun (LawfulElgotMonad.naturality (round (ε := ε) s)
        (fun label => pure (encodeLabel [E,D] label))) env.2).symm)
  rw [ev] at h
  have back := congrArg (fun value : m (CategoricalLabelDen [E,D]) =>
    value >>= fun label => pure ((encodeLabel [E,D]).symm label)) h
  simpa only [bind_assoc, pure_bind, Equiv.symm_apply_apply, bind_pure] using back.symm

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Proofs
