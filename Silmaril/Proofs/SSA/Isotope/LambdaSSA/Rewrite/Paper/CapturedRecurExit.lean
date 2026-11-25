module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms

/-! # Compute the categorical denotation of the actual captured block -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.CapturedRecurExit
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (contextualStep extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind caseWithContext extend retainLeft)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher
open CartesianMonoidalCategory (fst snd lift)

private abbrev innerΓ : VCtx (Ty Empty) := [Flag, Flag, Carry]
private abbrev armΓ : VCtx (Ty Empty) := U :: innerΓ

private def repeatValue : obj Exit := .inl (.inr PUnit.unit)
private def exitValue (c : Bits) : obj Exit := .inr (.inl c)

private noncomputable def repeatArm : (J).obj (ctxObj M armΓ) ⟶ (J).obj (labelObj M [Exit]) :=
  (J).map (↾fun _ => repeatValue) ≫ (J).map (labelInject M 0 rfl)

private noncomputable def exitArm : (J).obj (ctxObj M armΓ) ⟶ (J).obj (labelObj M [Exit]) :=
  (J).map (↾fun p => exitValue p.1.1.2) ≫ (J).map (labelInject M 0 rfl)

private noncomputable def caseBody : (J).obj (ctxObj M innerΓ) ⟶ (J).obj (labelObj M [Exit]) :=
  caseWithContext J ((J).map (lookup M 0 (rfl : At innerΓ 0 Flag)) ≫
    (J).map (M.coprodIso U U).hom) repeatArm exitArm

private noncomputable def graphArrow : (J).obj (ctxObj M [Carry]) ⟶ (J).obj (labelObj M [Exit]) :=
  bind J ((J).map (lookup M 0 (rfl : At [Carry] 0 Carry)))
    ((J).map ((𝟙 _) ⊗ₘ (M.productIso Flag Flag).hom) ≫
      (J).map (ctxPairIso M [Carry] Flag Flag).hom ≫ caseBody)

private theorem injectLeft (A B : Ty Empty) :
    (coprod.inl : M.obj A ⟶ _) ≫ (M.coprodIso A B).inv =
      (↾Sum.inl : obj A ⟶ obj (.coprod A B)) :=
  Types.binaryCoproductIso_inl_comp_hom (obj A) (obj B)

private theorem injectRight (A B : Ty Empty) :
    (coprod.inr : M.obj B ⟶ _) ≫ (M.coprodIso A B).inv =
      (↾Sum.inr : obj B ⟶ obj (.coprod A B)) :=
  Types.binaryCoproductIso_inr_comp_hom (obj A) (obj B)

set_option backward.isDefEq.respectTransparency false in
private theorem blockArrow_unique {a : (J).obj (ctxObj M [Carry]) ⟶ (J).obj (labelObj M [Exit])}
    (d : RegionDenotes J M blockBound.hasType a) : a = graphArrow := by
  change RegionDenotes J M (r := .let₂ (.var 0) (.case (.var 0)
      (.br 0 (.inl (.inr .unit))) (.br 0 (.inr (.inl (.var 2)))))) _ a at d
  cases d with
  | let₂ scrut body =>
    cases scrut
    rename_i A B arrow typed loc
    have eq : Carry = Ty.product A B := Option.some.inj loc
    obtain ⟨rfl, rfl⟩ := Ty.product.inj eq
    cases body with
    | case ds dl dr =>
      cases ds
      rename_i A B fl fr hl hr scrutLoc
      have eqFlag : Flag = Ty.coprod A B := Option.some.inj scrutLoc
      obtain ⟨rfl, rfl⟩ := Ty.coprod.inj eqFlag
      cases dl with
      | br dt =>
        cases dt with
        | inl d =>
          cases d with
          | inr u =>
            cases u
            cases dr with
            | br dt =>
              cases dt with
              | inr d =>
                cases d with
                | inl v =>
                  cases v
                  rename_i B₁ A₁ locL A₂ X₂ B₂ locR locV
                  have ⟨e₁, e₂⟩ := Ty.coprod.inj (Option.some.inj locL :
                    Ty.coprod Flag (Ty.coprod Flag .empty) =
                      Ty.coprod (Ty.coprod A₁ U) B₁)
                  have ⟨e₃, _⟩ := Ty.coprod.inj e₁
                  have ⟨e₄, e₅⟩ := Ty.coprod.inj (Option.some.inj locR :
                    Ty.coprod Flag (Ty.coprod Flag .empty) =
                      Ty.coprod A₂ (Ty.coprod X₂ B₂))
                  have ⟨e₆, e₇⟩ := Ty.coprod.inj e₅
                  subst B₁ A₁ A₂ X₂ B₂
                  simp only [injectLeft, injectRight, ← (J).map_comp, graphArrow,
                    caseBody, repeatArm, exitArm]
                  rfl

private theorem comp_apply {X Y Z : Kleisli (ofTypeMonad MaybeT)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.of) :
    (f ≫ g).of x = ((show MaybeT Y.of from f.of x) >>= fun y => g.of y) :=
  congrFun (Kleisli.Type.comp_of_eq_kleisliRight MaybeT f g) x

private theorem map_apply {X Y : Type} (f : X ⟶ Y) (x : X) :
    ((J).map f).of x = (pure (f x) : MaybeT Y) := rfl

open Silmaril.Isotope.LetIter.Semantics.Categorical (routeEnvironment)

set_option backward.isDefEq.respectTransparency false in
private theorem case_at_inl {E A B D : Type} (p : E ⟶ A ⨿ B)
    (l : (J).obj (E ⊗ A) ⟶ (J).obj D) (r : (J).obj (E ⊗ B) ⟶ (J).obj D)
    (e : E) (a : A) (hp : p e = (coprod.inl : A ⟶ A ⨿ B) a) :
    (caseWithContext J ((J).map p) l r).of e = l.of (e, a) := by
  change (extend J ((J).map p) ≫ routeEnvironment J E A B ≫ coprod.desc l r).of e = _
  rw [extend_map, comp_apply, map_apply, pure_bind]
  change (routeEnvironment J E A B ≫ coprod.desc l r).of (e, p e) = _
  rw [hp]
  have h := congrArg
    (fun f => f ≫ coprod.desc l r) (route_inl J (E := E) (A := A) (B := B))
  rw [Category.assoc] at h
  have h := congrArg (fun f : (J).obj (E ⊗ A) ⟶ (J).obj D => f.of (e, a)) h
  rw [coprod.inl_desc] at h
  simp only [comp_apply, map_apply, pure_bind] at h ⊢
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem case_at_inr {E A B D : Type} (p : E ⟶ A ⨿ B)
    (l : (J).obj (E ⊗ A) ⟶ (J).obj D) (r : (J).obj (E ⊗ B) ⟶ (J).obj D)
    (e : E) (b : B) (hp : p e = (coprod.inr : B ⟶ A ⨿ B) b) :
    (caseWithContext J ((J).map p) l r).of e = r.of (e, b) := by
  change (extend J ((J).map p) ≫ routeEnvironment J E A B ≫ coprod.desc l r).of e = _
  rw [extend_map, comp_apply, map_apply, pure_bind]
  change (routeEnvironment J E A B ≫ coprod.desc l r).of (e, p e) = _
  rw [hp]
  have h := congrArg
    (fun f => f ≫ coprod.desc l r) (route_inr J (E := E) (A := A) (B := B))
  rw [Category.assoc] at h
  have h := congrArg (fun f : (J).obj (E ⊗ B) ⟶ (J).obj D => f.of (e, b)) h
  rw [coprod.inr_desc] at h
  simp only [comp_apply, map_apply, pure_bind] at h ⊢
  exact h

set_option backward.isDefEq.respectTransparency false in
theorem denoteBlock_apply (c s : Bits) :
    (denoteSingletonRegion J M blockBound.hasType).of (c, s) = Sum.inl (blockValue c s) := by
  rw [denoteSingletonRegion, blockArrow_unique (denoteRegion_spec J M blockBound.hasType)]
  unfold graphArrow LetIter.ProofRelevant.Semantics.Categorical.bind caseBody
  rw [extend_map, ← (J).map_comp]
  simp only [Category.assoc, comp_apply, map_apply, pure_bind]
  change ((show MaybeT (labelObj M [Exit]) from (caseWithContext J ((J).map (lookup M 0 (rfl : At innerΓ 0 Flag) ≫ (M.coprodIso U U).hom))
    repeatArm exitArm).of (((PUnit.unit, (c, s)), c), s)) >>=
      fun a => (Sum.inl (singletonLabelPayload M Exit a) : MaybeT (obj Exit))) = _
  cases s with
  | inl u =>
    rw [case_at_inl _ _ _ _ u (by
      change (Types.binaryCoproductIso PUnit PUnit).inv (.inl u) = _
      exact congrArg (fun f : PUnit ⟶ PUnit ⨿ PUnit => f u)
        (Types.binaryCoproductIso_inl_comp_inv PUnit PUnit))]
    have h := congrArg (fun f : obj Exit ⟶ obj Exit => f repeatValue) (labelInject_payload M Exit)
    simp only [repeatArm, comp_apply, map_apply]
    exact congrArg Sum.inl h
  | inr u =>
    rw [case_at_inr _ _ _ _ u (by
      change (Types.binaryCoproductIso PUnit PUnit).inv (.inr u) = _
      exact congrArg (fun f : PUnit ⟶ PUnit ⨿ PUnit => f u)
        (Types.binaryCoproductIso_inr_comp_inv PUnit PUnit))]
    have h := congrArg (fun f : obj Exit ⟶ obj Exit => f (exitValue c)) (labelInject_payload M Exit)
    simp only [exitArm, comp_apply, map_apply]
    exact congrArg Sum.inl h

private theorem denote_block_map :
    denoteSingletonRegion J M blockBound.hasType = (J).map (↾fun p => blockValue p.1 p.2) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext p
  exact denoteBlock_apply p.1 p.2

set_option backward.isDefEq.respectTransparency false in
theorem retainedBlock_apply (outer c s : Bits) :
    (J.map (M.productIso Flag Carry).hom ≫
      retainLeft J (R := M.obj Flag) (denoteSingletonRegion J M blockBound.hasType) ≫
      J.map (M.productIso Flag Exit).inv).of (outer, (c, s)) =
        (Sum.inl (outer, blockValue c s) : MaybeT (Bits × obj Exit)) := by
  let f : obj Carry ⟶ obj Exit := ↾fun p => blockValue p.1 p.2
  have retain : retainLeft J (R := M.obj Flag) (J.map f) = J.map (M.obj Flag ◁ f) := by
    simp [retainLeft, PremonoidalCategory.leftTensor, Functor.StrongPremonoidal.tensor_naturality_right]
  rw [denote_block_map]
  change (J.map (M.productIso Flag Carry).hom ≫ retainLeft J (R := M.obj Flag) (J.map f) ≫
    J.map (M.productIso Flag Exit).inv).of (outer, (c, s)) = _
  rw [retain]
  simp only [← J.map_comp]
  rfl

private theorem unpackInput (c s : Bits) :
    (carriedIso M Flag Flag).hom (stateInput c s) = (c, s) := by
  have h := congrArg (fun f : Bits ⟶ Bits => f s) (labelInject_payload M Flag)
  change (c, (singletonLabelPayload M Flag) (labelInject M 0 (rfl : At [Flag] 0 Flag) s)) = (c, s)
  exact Prod.ext rfl h

private noncomputable def exitSplit : M.obj Exit ⟶ Live ⨿ Live :=
  unpackLabel M [Flag, Flag] ≫ labelAppendSplit M [Flag] [Flag]

set_option backward.isDefEq.respectTransparency false in
private theorem exitSplit_repeat (s : Bits) :
    exitSplit (.inl s) = (coprod.inr : Live ⟶ Live ⨿ Live)
      (labelInject M 0 (rfl : At [Flag] 0 Flag) s) := by
  have h : (↾Sum.inl : Bits ⟶ obj Exit) ≫ exitSplit =
      labelInject M 0 (rfl : At [Flag] 0 Flag) ≫ coprod.inr := by
    rw [← injectLeft Flag (.coprod Flag .empty)]
    simp only [exitSplit, packedExitType, unpackLabel, coprod_ty, empty_ty, Category.assoc, Iso.inv_hom_id_assoc,
      coprod.inl_desc_assoc, labelAppendSplit_zero]
  exact congrArg (fun f : Bits ⟶ Live ⨿ Live => f s) h

set_option backward.isDefEq.respectTransparency false in
private theorem exitSplit_done (c : Bits) :
    exitSplit (.inr (.inl c)) = (coprod.inl : Live ⟶ Live ⨿ Live)
      (labelInject M 0 (rfl : At [Flag] 0 Flag) c) := by
  have h : (↾Sum.inl : Bits ⟶ obj (.coprod Flag .empty)) ≫ (↾Sum.inr : obj (.coprod Flag .empty) ⟶ obj Exit) ≫ exitSplit =
      labelInject M 0 (rfl : At [Flag] 0 Flag) ≫ coprod.inl := by
    rw [← injectLeft Flag .empty, ← injectRight Flag (.coprod Flag .empty)]
    simp only [exitSplit, packedExitType, unpackLabel, coprod_ty, empty_ty, Category.assoc, Iso.inv_hom_id_assoc,
      coprod.inr_desc_assoc, coprod.inl_desc_assoc, labelInject_labelMap_assoc, labelAppendSplit_succ]
  exact congrArg (fun f : Bits ⟶ Live ⨿ Live => f c) h

set_option backward.isDefEq.respectTransparency false in
private theorem route_exact_inl (e : Capture) (a : Live) :
    (routeEnvironment J Capture Live Live ≫
        (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom).of
      (e, (coprod.inl : Live ⟶ Live ⨿ Live) a) = (Sum.inl (Sum.inl (e, a)) : MaybeT (Carried ⊕ Carried)) := by
  have h := congrArg (fun g => g ≫ (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom)
    (route_inl J (E := Capture) (A := Live) (B := Live))
  rw [Category.assoc, Kleisli.Type.inl_coprodIsoSum_hom] at h
  have h := congrArg (fun f : (J).obj Carried ⟶ _ => f.of (e, a)) h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem route_exact_inr (e : Capture) (a : Live) :
    (routeEnvironment J Capture Live Live ≫
        (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom).of
      (e, (coprod.inr : Live ⟶ Live ⨿ Live) a) = (Sum.inl (Sum.inr (e, a)) : MaybeT (Carried ⊕ Carried)) := by
  have h := congrArg (fun g => g ≫ (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom)
    (route_inr J (E := Capture) (A := Live) (B := Live))
  rw [Category.assoc, Kleisli.Type.inr_coprodIsoSum_hom] at h
  have h := congrArg (fun f : (J).obj Carried ⟶ _ => f.of (e, a)) h
  exact h

open Silmaril.Isotope.LetIter.Semantics.Categorical (retainEnvironment_map)

set_option backward.isDefEq.respectTransparency false in
theorem exactStep_apply (c s : Bits) :
    exactStep.of (stateInput c s) =
      (Sum.inl (match s with
        | .inl _ => Sum.inr (stateInput c (.inr PUnit.unit))
        | .inr _ => Sum.inl (stateInput c c)) : MaybeT (Carried ⊕ Carried)) := by
  unfold exactStep actualStep contextualStep blockComputation
  rw [denote_block_map, ← (J).map_comp, ← (J).map_comp, retainEnvironment_map, Category.assoc]
  let l : Carried ⟶ Live ⨿ Live :=
    (carriedIso M Flag Flag).hom ≫ (↾fun p => blockValue p.1 p.2) ≫ exitSplit
  let r : (J).obj (Capture ⊗ (Live ⨿ Live)) ⟶ Kleisli.mk (ofTypeMonad MaybeT) (Carried ⊕ Carried) :=
    routeEnvironment J Capture Live Live ≫
      (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom
  change ((J).map (lift (fst Capture Live) l) ≫ r).of (stateInput c s) = _
  rw [comp_apply, map_apply, pure_bind]
  change (routeEnvironment J Capture Live Live ≫
    (Kleisli.Type.coprodIsoSum MaybeT ((J).obj Carried) ((J).obj Carried)).hom).of
      ((PUnit.unit, c), exitSplit (blockValue ((carriedIso M Flag Flag).hom (stateInput c s)).1
        ((carriedIso M Flag Flag).hom (stateInput c s)).2)) = _
  rw [unpackInput]
  cases s with
  | inl a =>
    change _ = (Sum.inl (Sum.inr (stateInput c (.inr PUnit.unit))) : MaybeT (Carried ⊕ Carried))
    rw [show blockValue c (.inl a) = Sum.inl (Sum.inr PUnit.unit) from rfl, exitSplit_repeat]
    exact route_exact_inr _ _
  | inr a =>
    change _ = (Sum.inl (Sum.inl (stateInput c c)) : MaybeT (Carried ⊕ Carried))
    rw [show blockValue c (.inr a) = Sum.inr (Sum.inl c) from rfl, exitSplit_done]
    exact route_exact_inl _ _

set_option backward.isDefEq.respectTransparency false in
theorem iterate_apply (c s : Bits) :
    (CategoryTheory.iterate actualStep).of (stateInput c s) = (Sum.inl (stateInput c c) : MaybeT Carried) := by
  rw [Kleisli.Type.iterate_of]
  let f : Carried → MaybeT (Carried ⊕ Carried) := exactStep.of
  change Elgot.iter f (stateInput c s) = _
  have step := Elgot.LawfulElgotMonad.fixpoint (m := MaybeT) f
  have onExit (u : PUnit) : Elgot.iter f (stateInput c (.inr u)) = Sum.inl (stateInput c c) := by
    have h := congrFun step (stateInput c (.inr u))
    change Elgot.iter f (stateInput c (.inr u)) =
      (f (stateInput c (.inr u)) >>= Sum.elim pure (Elgot.iter f)) at h
    rw [show f (stateInput c (.inr u)) = Sum.inl (Sum.inl (stateInput c c)) from
      exactStep_apply c (.inr u)] at h
    exact h
  cases s with
  | inr u => exact onExit u
  | inl u =>
    have h := congrFun step (stateInput c (.inl u))
    change Elgot.iter f (stateInput c (.inl u)) =
      (f (stateInput c (.inl u)) >>= Sum.elim pure (Elgot.iter f)) at h
    rw [show f (stateInput c (.inl u)) = Sum.inl (Sum.inr (stateInput c (.inr PUnit.unit))) from
      exactStep_apply c (.inl u)] at h
    exact h.trans (onExit PUnit.unit)

set_option backward.isDefEq.respectTransparency false in
theorem iterate_repacked_apply (c s : Bits) :
    ((J).map (carriedIso M Flag Flag).inv ≫
      CategoryTheory.iterate actualStep ≫
      (J).map (carriedIso M Flag Flag).hom).of (c, s) =
        (Sum.inl (c, c) : MaybeT (Bits × Bits)) := by
  have e := congrArg (fun f : Carried ⟶ Carried => f (stateInput c s))
    (carriedIso M Flag Flag).hom_inv_id
  have es : (carriedIso M Flag Flag).inv (c,s) = stateInput c s :=
    (congrArg (fun p => (carriedIso M Flag Flag).inv p) (unpackInput c s).symm).trans e
  simp only [comp_apply, map_apply, pure_bind, es, iterate_apply]
  change Sum.inl ((carriedIso M Flag Flag).hom (stateInput c c)) = _
  rw [unpackInput]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CapturedRecurExit
