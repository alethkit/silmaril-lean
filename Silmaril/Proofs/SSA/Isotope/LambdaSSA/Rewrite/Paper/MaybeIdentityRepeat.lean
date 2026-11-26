module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Repeat.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Repeat.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Divergence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Computing the actual pure repeat block in the Maybe model -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.CapturedRecurExit
open scoped Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Paper.SingletonReification.SingleCfg.Model (contextualStep_identityRepeat_of_packed)
open Paper.WithProjectionReturnsAndUnitEta.Reification
  (repeatStateBlock canonicalIterate canonicalIterate_repeat_naturality)
open Paper.Extension.Singleton (ofType emptyIsInitial)
open CfgEta.TypeCategory.ConstructorReification (sndMap inlMap)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload)
open Silmaril.Isotope.LetIter.Semantics.Categorical (extend_map)
open CartesianMonoidalCategory (snd)

local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
local notation "Obj" => ofType (Seed)

set_option backward.isDefEq.respectTransparency false in
private theorem repeat_graph {f : J.obj (ctxObj M [Carry]) ⟶ J.obj (labelObj M [Exit])}
    (d : RegionDenotes J M (repeatStateBlock (Φ := Empty) Flag Flag Flag).hasType f) :
    f = J.map (snd (𝟙_ Type) (M.obj Carry) ≫ sndMap M Flag Flag ≫ inlMap M Flag (coprod Flag Silmaril.empty) ≫
      labelInject M 0 (L := [Exit]) rfl) := by
  change RegionDenotes J M (r := .let₂ (.var 0) (.br 0 (.inl (.var 0)))) _ f at d
  cases d with
  | let₂ scrut body =>
    cases scrut
    rename_i A B fb hb loc
    have ty : Carry = Ty.product A B := Option.some.inj loc
    obtain ⟨rfl, rfl⟩ := Ty.product.inj ty
    cases body with
    | br dt =>
      cases dt with
      | inl dv =>
        cases dv
        rename_i A B label _
        have tagTy : Exit = Ty.coprod A B := Option.some.inj label
        obtain ⟨rfl, rfl⟩ := Ty.coprod.inj tagTy
        let E := ctxObj M [Carry]
        let c := snd (𝟙_ Type) (M.obj Carry)
        let pay := lookup M 0 (rfl : At [Flag, Flag, Carry] 0 Flag)
        let tag := inlMap M Flag (coprod Flag Silmaril.empty)
        let put := labelInject M 0 (L := [Exit]) (A := Exit) rfl
        change Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J (J.map c)
          (J.map (𝟙 E ⊗ₘ (M.productIso Flag Flag).hom) ≫ J.map (ctxPairIso M [Carry] Flag Flag).hom ≫
            (J.map pay ≫ J.map tag) ≫ J.map put) = J.map (c ≫ sndMap M Flag Flag ≫ tag ≫ put)
        rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map]
        simp only [Category.assoc, ← J.map_comp]
        have lookupPair : (ctxPairIso M [Carry] Flag Flag).hom ≫ pay =
            snd E (M.obj Flag ⊗ M.obj Flag) ≫ snd (M.obj Flag) (M.obj Flag) :=
          CartesianMonoidalCategory.associator_inv_snd E (M.obj Flag) (M.obj Flag)
        rw [reassoc_of% lookupPair, CartesianMonoidalCategory.tensorHom_snd_assoc,
          CartesianMonoidalCategory.lift_snd_assoc]
        rfl

set_option backward.isDefEq.respectTransparency false in
theorem identityRepeatStep_eq :
    identityRepeatStep = coprod.inr := by
  let hb := repeatStateBlock (Φ := Empty) Flag Flag Flag
  have h := repeat_graph (denoteRegion_spec J M hb.hasType)
  apply contextualStep_identityRepeat_of_packed J M hb
  rw [denoteSingletonRegion, h, ← J.map_comp_assoc]
  simp only [Category.assoc, ← J.map_comp]
  change J.map ((λ_ (M.obj Carry)).inv ≫ snd (𝟙_ Type) (M.obj Carry) ≫
    sndMap M Flag Flag ≫ inlMap M Flag (coprod Flag Silmaril.empty) ≫ labelInject M 0 (L := [Exit]) rfl ≫
    singletonLabelPayload M Exit) = _
  rw [CartesianMonoidalCategory.leftUnitor_inv_snd_assoc, labelInject_payload M Exit]
  exact congrArg (fun f => J.map (sndMap M Flag Flag ≫ f))
    (Category.comp_id (inlMap M Flag (coprod Flag Silmaril.empty)))

set_option backward.isDefEq.respectTransparency false in
private theorem iterate_at_empty {A B : Type}
    (out : J.obj PEmpty ⟶ J.obj B) :
    CategoryTheory.iterate (coprod.inr : J.obj A ⟶ J.obj PEmpty ⨿ J.obj A) ≫ out =
      CategoryTheory.iterate (coprod.inr : J.obj A ⟶ J.obj B ⨿ J.obj A) := by
  rw [ElgotCategory.naturality, coprod.inr_map, Category.id_comp]

theorem identityRepeat_iterate_apply (input : Carried) :
    (CategoryTheory.iterate identityRepeatStep).of input = (Sum.inr PUnit.unit : MaybeT Carried) := by
  rw [identityRepeatStep_eq, ← iterate_at_empty (J.map (Types.isInitialPEmpty.to Carried))]
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  let noExit : MaybeT PEmpty :=
    (CategoryTheory.iterate (coprod.inr : J.obj Carried ⟶ J.obj PEmpty ⨿ J.obj Carried)).of input
  let out : PEmpty → MaybeT Carried := (J.map (Types.isInitialPEmpty.to Carried)).of
  change (noExit >>= out) = _
  rw [maybeEmpty_value noExit]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem identityRepeat_repacked_eq_image :
    J.map (carriedIso M Flag Flag).inv ≫ CategoryTheory.iterate identityRepeatStep ≫
      J.map (carriedIso M Flag Flag).hom =
        denoteJoinedEmpty Carry (canonicalIterate (coprod.inr : Obj Carry ⟶ Obj (.empty : Ty Empty) ⨿ Obj Carry)) ≫
          J.map (M.emptyIsInitial.to (M.obj Carry)) := by
  let out := Types.isInitialPEmpty.to Carried
  let rawZero := CategoryTheory.iterate (coprod.inr : J.obj Carried ⟶ J.obj PEmpty ⨿ J.obj Carried)
  let image := denoteJoinedEmpty Carry
    (canonicalIterate (coprod.inr : Obj Carry ⟶ Obj (.empty : Ty Empty) ⨿ Obj Carry))
  have left : J.map (carriedIso M Flag Flag).inv ≫ rawZero = image :=
    @Subsingleton.elim _ (maybeEmpty_hom (M.obj Carry)) _ _
  have right : J.map out ≫ J.map (carriedIso M Flag Flag).hom =
      J.map (M.emptyIsInitial.to (M.obj Carry)) := by
    rw [← Functor.map_comp]
    exact congrArg J.map (M.emptyIsInitial.hom_ext _ _)
  rw [identityRepeatStep_eq, ← iterate_at_empty (J.map out)]
  change J.map (carriedIso M Flag Flag).inv ≫ (rawZero ≫ J.map out) ≫ J.map (carriedIso M Flag Flag).hom =
    image ≫ J.map (M.emptyIsInitial.to (M.obj Carry))
  rw [Category.assoc rawZero, right, ← Category.assoc, left]

set_option backward.isDefEq.respectTransparency false in
theorem guardedRepeat_factorsThroughEmpty (A B : Ty Empty) :
    canonicalIterate (coprod.inr : Obj A ⟶ Obj B ⨿ Obj A) =
      canonicalIterate (coprod.inr : Obj A ⟶ Obj (.empty : Ty Empty) ⨿ Obj A) ≫
        (emptyIsInitial (Seed)).to (Obj B) := by
  simpa only [Category.id_comp] using!
    (canonicalIterate_repeat_naturality (A := Obj A) (T := Obj (.empty : Ty Empty)) (B := Obj B)
      (𝟙 _) ((emptyIsInitial (Seed)).to (Obj B))).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.MaybeIdentityRepeat
