module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Example.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Distributive.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Realization.Reification.Thms

/-! # The two guarded phases of the captured repeat/exit block -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCapturedRecurExit

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.SingletonReification.SingleCfg
open Paper.SingletonReification.SingleCfg.CapturedRecurExit
open scoped Paper.SingletonReification.SingleCfg.CapturedRecurExit
open Paper.TypeCategory
open CfgEta.TypeCategory (seqValueBranches whiskerLeftRegion whiskerLeftRegion_typed)
open CategoryTheory CategoryTheory.Limits

local notation "baseRegion" => ofRegion (τ := Ty Empty)
local notation "baseObj" => ofType (Φ := Empty)

private abbrev Row : Ty Empty := .product Flag U
private abbrev Args : VCtx (Ty Empty) := [U, Flag, Row]
private abbrev Kept : Ty Empty := .product Flag Exit

private def phaseTag (right : Bool) (a : Tm Empty) : Tm Empty :=
  if right then .inr a else .inl a

private def beforeRoute (right : Bool) : Region Empty :=
  let row := whiskerLeftRegion (.br 0 (phaseTag right (.var 0)))
  let pref := compLSubst (fun _ => row) (fun _ => duplicateCapture) 0
  compLSubst (fun _ => pref) (fun _ => whiskerLeftRegion block) 0

private def keptCase (scrut : Tm Empty) (capture : Nat) : Region Empty :=
  .case scrut (.br 0 (.pair (.var capture) (.inl (.inr .unit))))
    (.br 0 (.pair (.var capture) (.inr (.inl (.var 2)))))

private theorem retainedBody {Γ : VCtx (Ty Empty)} :
    HasType (Carry :: Flag :: Γ) (.let₂ (.var 0) (keptCase (.var 0) 4)) [Kept] :=
  .let₂ (.var (i := 0) (A := Carry) rfl)
    (.case (.var (i := 0) (A := Flag) rfl)
      (.br rfl (.pair (.var (i := 4) rfl) (.inl (.inr .unit))))
      (.br rfl (.pair (.var (i := 4) rfl) (.inr (.inl (.var (i := 2) rfl))))))

private theorem afterTaggedPair :
    HasType (Flag :: Flag :: Args)
      (.let₂ (.pair (.var 1) (.pair (.var 1) (.var 0)))
        (.let₂ (.var 0) (keptCase (.var 0) 4))) [Kept] :=
  .let₂ (.pair (.var (i := 1) (A := Flag) rfl) (.pair (.var (i := 1) (A := Flag) rfl)
    (.var (i := 0) (A := Flag) rfl))) retainedBody

private def packedValue (right : Bool) (cap : Tm Empty) : Tm Empty :=
  if right then .inr (.inl cap) else .inl (.inr .unit)

private theorem packedValue_typed (right : Bool) :
    Tm.BranchValue Args (packedValue right (.var 1)) Exit := by
  cases right
  · exact .inl (.inr .unit)
  · exact .inr (.inl (.var (i := 1) rfl))

private theorem phaseTag_typed (right : Bool) :
    Tm.BranchValue Args (phaseTag right (.var 0)) Flag := by
  cases right
  · exact .inl (.var (i := 0) rfl)
  · exact .inr (.var (i := 0) rfl)

set_option backward.isDefEq.respectTransparency false in
private theorem beforeRoute_normal (right : Bool) :
    Paper.Eqv [Row] (beforeRoute right)
      (.let₂ (.var 0) (.br 0 (.pair (.var 1) (packedValue right (.var 1))))) [Kept] := by
  apply Paper.Eqv.let₂ (.var (i := 0) (rfl : At [Row] 0 Row))
  let cap : Tm.BranchValue Args (.var 1 : Tm Empty) Flag := .var (i := 1) rfl
  let tag := phaseTag_typed right
  -- The phase input, retained capture and original block introduce three product binders.
  have b₁ := Paper.Eqv.productBeta (.let₂Beta cap tag afterTaggedPair)
  have b₂ := Paper.Eqv.productBeta (.let₂Beta cap (.pair cap tag) (retainedBody (Γ := Args)))
  have caseTyped : HasType (Flag :: Flag :: Args) (keptCase (.var 0) 4) [Kept] :=
    .case (.var (i := 0) (A := Flag) rfl)
      (.br rfl (.pair (.var (i := 4) rfl) (.inl (.inr .unit))))
      (.br rfl (.pair (.var (i := 4) rfl) (.inr (.inl (.var (i := 2) rfl)))))
  have b₃ := Paper.Eqv.productBeta (.let₂Beta cap tag caseTyped)
  let arg : Tm.BranchValue Args (.var 0 : Tm Empty) U := .var (i := 0) rfl
  have l : HasType (U :: Args) (.br 0 (.pair (.var 2) (.inl (.inr .unit))) : Region Empty) [Kept] :=
    .br rfl (.pair (.var (i := 2) rfl) (.inl (.inr .unit)))
  have r : HasType (U :: Args) (.br 0 (.pair (.var 2) (.inr (.inl (.var 2)))) : Region Empty) [Kept] :=
    .br rfl (.pair (.var (i := 2) rfl) (.inr (.inl (.var (i := 2) rfl))))
  cases right
  · exact b₁.trans (b₂.trans (b₃.trans
      (.cfgEta (.native ((SubstitutionEquiv.base (.caseInl arg.hasType l r)).trans (.letValue arg l))))))
  · exact b₁.trans (b₂.trans (b₃.trans
      (.cfgEta (.native ((SubstitutionEquiv.base (.caseInr arg.hasType l r)).trans (.letValue arg r))))))

private theorem phaseIn_typed (right : Bool) :
    ValueBranches [U] (.br 0 (phaseTag right (.var 0))) [Flag] := by
  cases right
  · exact .br rfl (.inl (.var (i := 0) rfl))
  · exact .br rfl (.inr (.var (i := 0) rfl))

private theorem normalized_typed (right : Bool) :
    ValueBranches [Row] (.let₂ (.var 0) (.br 0 (.pair (.var 1) (packedValue right (.var 1))))) [Kept] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.pair (.var (i := 1) rfl) (packedValue_typed right)))

private def outcome (right : Bool) : Tm Empty :=
  if right then .var 1 else .inr .unit

private theorem outcome_typed (right : Bool) : Tm.BranchValue Args (outcome right) Flag := by
  cases right
  · exact .inr .unit
  · exact .var (i := 1) rfl

private theorem phaseOut_typed (right : Bool) :
    ValueBranches [Row] (.let₂ (.var 0) (.br 0 (.pair (.var 1) (outcome right)))) [Carry] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.pair (.var (i := 1) rfl) (outcome_typed right)))

private def exitTag (right : Bool) (a : Tm Empty) : Tm Empty :=
  if right then .inr (.inl a) else .inl a

private theorem exitTag_typed {Γ : VCtx (Ty Empty)} {a : Tm Empty}
    (right : Bool) (ha : Tm.BranchValue Γ a Flag) :
    Tm.BranchValue Γ (exitTag right a) Exit := by
  cases right
  · exact .inl ha
  · exact .inr (.inl ha)

private theorem packArm_typed (right : Bool) :
    ValueBranches [Flag] (.br 0 (exitTag right (.var 0))) [Exit] :=
  .br rfl (exitTag_typed right (.var (i := 0) rfl))

set_option backward.isDefEq.respectTransparency false in
private theorem prefix_normal (right : Bool) :
    (whiskerLeft (baseObj Flag) (baseRegion (phaseIn_typed right)) ≫
      baseRegion (duplicateCapture_typed (Φ := Empty) Flag Flag)) ≫ whiskerLeft (baseObj Flag) (ofRegion blockBound) =
        baseRegion (normalized_typed right) := by
  let p := whiskerLeftRegion_typed Flag (phaseIn_typed right)
  let q := duplicateCapture_typed (Φ := Empty) Flag Flag
  let b := whiskerLeftRegion_typed Flag blockBound
  rw [whiskerLeft_ofRegion, whiskerLeft_ofRegion, ofRegion_comp p q (seqValueBranches p q),
    ofRegion_comp (seqValueBranches p q) b (seqValueBranches (seqValueBranches p q) b)]
  exact (ofRegion_eq_iff _ _).2 (beforeRoute_normal right)

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_pack (right : Bool) :
    baseRegion (phaseOut_typed right) ≫ whiskerLeft (baseObj Flag) (baseRegion (packArm_typed right)) =
      baseRegion (normalized_typed right) := by
  let p := phaseOut_typed right
  let q := whiskerLeftRegion_typed Flag (packArm_typed right)
  rw [whiskerLeft_ofRegion, ofRegion_comp p q (seqValueBranches p q)]
  apply (ofRegion_eq_iff _ _).2
  apply Paper.Eqv.let₂ (.var (i := 0) (rfl : At [Row] 0 Row))
  have bind : HasType (Flag :: Flag :: Args)
      (.br 0 (.pair (.var 1) (exitTag right (.var 0)))) [Kept] :=
    .br rfl (.pair (.var (i := 1) rfl) (exitTag_typed right (.var (i := 0) (rfl : At (Flag :: Flag :: Args) 0 Flag))).hasType)
  have h := Paper.Eqv.productBeta (.let₂Beta (.var (i := 1) (rfl : At Args 1 Flag)) (outcome_typed right) bind)
  cases right <;> exact h

set_option backward.isDefEq.respectTransparency false in
private theorem rankRow (right : Bool) :
    whiskerLeft (baseObj Flag) (baseRegion (phaseIn_typed right)) ≫
      baseRegion (realizePackedStep_typed blockBound) =
    baseRegion (phaseOut_typed right) ≫
      (if right then (sumCofan (Φ := Empty) Carry Carry).inl else (sumCofan (Φ := Empty) Carry Carry).inr) := by
  let retag := baseRegion (retagPacked_typed (Φ := Empty) Flag Flag Flag)
  have factor :
      whiskerLeft (baseObj Flag) (baseRegion (phaseIn_typed right)) ≫
        baseRegion (realizePackedStep_typed blockBound) =
          baseRegion (normalized_typed right) ≫ retag := by
    rw [← realizePackedStep_arrow blockBound, ← Category.assoc, ← Category.assoc, prefix_normal]
  have routed : whiskerLeft (baseObj Flag) (baseRegion (packArm_typed right)) ≫ retag =
      (if right then (sumCofan (Φ := Empty) Carry Carry).inl else (sumCofan (Φ := Empty) Carry Carry).inr) := by
    have repeatTag : baseRegion (packArm_typed false) ≫ baseRegion (exitDecoder_typed Flag Flag) =
        (sumCofan (Φ := Empty) Flag Flag).inr := by
      simpa only [sumCofan_inl] using! exitDecoder_inl (Φ := Empty) Flag Flag
    have resultTag : baseRegion (packArm_typed true) ≫ baseRegion (exitDecoder_typed Flag Flag) =
        (sumCofan (Φ := Empty) Flag Flag).inl := by
      have packed : (sumCofan (Φ := Empty) Flag (.empty : Ty Empty)).inl ≫
          (sumCofan (Φ := Empty) Flag (.coprod Flag .empty)).inr =
        baseRegion (packArm_typed true) := by
        rw [sumCofan_inl, sumCofan_inr]
        rfl
      rw [← packed, Category.assoc]
      exact exitDecoder_inr_inl (Φ := Empty) Flag Flag
    rw [show retag = _ from (retagPacked_distributor (Φ := Empty) Flag Flag Flag).symm,
      ← Category.assoc, ← whiskerLeft_comp]
    cases right
    · rw [repeatTag, Paper.RetainedCase.left_distributor_inr]
      rfl
    · rw [resultTag, Paper.RetainedCase.left_distributor_inl]
      rfl
  exact factor.trans ((congrArg (· ≫ retag) (normalized_pack right).symm).trans
    ((Category.assoc _ _ _).trans (congrArg (baseRegion (phaseOut_typed right) ≫ ·) routed)))

private theorem reset_typed :
    ValueBranches [Row] (.let₂ (.var 0) (.br 0 (.pair (.var 1) .unit)) : Region Empty) [Row] :=
  .let₂ (.var (i := 0) rfl) (.br rfl (.pair (.var (i := 1) rfl) .unit))

set_option backward.isDefEq.respectTransparency false in
private theorem repeat_reset :
    baseRegion reset_typed ≫ whiskerLeft (baseObj Flag)
      (baseRegion (phaseIn_typed true)) = baseRegion (phaseOut_typed false) := by
  let r := whiskerLeftRegion_typed Flag (phaseIn_typed true)
  rw [whiskerLeft_ofRegion, ofRegion_comp reset_typed r (seqValueBranches reset_typed r)]
  apply (ofRegion_eq_iff _ _).2
  apply Paper.Eqv.let₂ (.var (i := 0) (rfl : At [Row] 0 Row))
  have h : HasType (U :: Flag :: Args)
      (.br 0 (.pair (.var 1) (.inr (.var 0))) : Region Empty) [Carry] :=
    .br rfl (.pair (.var (i := 1) rfl) (.inr (.var (i := 0) rfl)))
  exact .productBeta (.let₂Beta (.var (i := 1) (rfl : At Args 1 Flag)) .unit h)

open Paper.WithProjectionReturnsAndUnitEta.Reification

local notation "JoinedSeed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
local notation "joinedObj" => Paper.Extension.Singleton.ofType JoinedSeed
local notation "proj" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := Ty Empty) (Φ := Empty)

private noncomputable abbrev phaseColimit :=
  Paper.Extension.Singleton.CoproductDistributivity.whiskeredSumIsColimit JoinedSeed Flag U U

private noncomputable abbrev phaseCover : joinedObj Row ⨿ joinedObj Row ≅ joinedObj Carry :=
  (phaseColimit.coconePointUniqueUpToIso (colimit.isColimit _)).symm

private noncomputable abbrev guardedStep : joinedObj Carry ⟶ joinedObj Carry ⨿ joinedObj Carry :=
  Paper.Extension.Singleton.ofRegion JoinedSeed (realizePackedStep_typed blockBound) ≫
    (Paper.Extension.Singleton.sumIso JoinedSeed Carry Carry).hom

set_option backward.isDefEq.respectTransparency false in
private theorem repeatCover :
    coprod.inl ≫ phaseCover.hom = (proj).map (whiskerLeft (baseObj Flag)
      (baseRegion (phaseIn_typed false))) := by
  apply (cancel_mono phaseCover.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := phaseColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.left⟩
  change (Paper.Extension.Singleton.whiskerLeftFunctor JoinedSeed (joinedObj Flag)).map
    ((proj).map (sumCofan (Φ := Empty) U U).inl) ≫ phaseCover.inv = coprod.inl at h
  rw [Paper.Extension.Singleton.whiskerLeft_map, sumCofan_inl] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem resultCover :
    coprod.inr ≫ phaseCover.hom = (proj).map (whiskerLeft (baseObj Flag)
      (baseRegion (phaseIn_typed true))) := by
  apply (cancel_mono phaseCover.inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h := phaseColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) ⟨WalkingPair.right⟩
  change (Paper.Extension.Singleton.whiskerLeftFunctor JoinedSeed (joinedObj Flag)).map
    ((proj).map (sumCofan (Φ := Empty) U U).inr) ≫ phaseCover.inv = coprod.inr at h
  rw [Paper.Extension.Singleton.whiskerLeft_map, sumCofan_inr] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem capturedRecurExit_unroll_two :
    ∃ out : joinedObj Carry ⟶ joinedObj Carry, ∀ tail,
      unroll (Paper.Extension.Singleton.ofRegion JoinedSeed (realizePackedStep_typed blockBound) ≫
        (Paper.Extension.Singleton.sumIso JoinedSeed Carry Carry).hom) tail 2 = out := by
  let next := (proj).map (baseRegion reset_typed)
  let out := (proj).map (baseRegion (phaseOut_typed true))
  refine ⟨phaseCover.inv ≫ coprod.desc (next ≫ out) out, fun tail => ?_⟩
  apply unroll_two_phases phaseCover guardedStep next out
  · have eq := congrArg (fun f => (proj).map f ≫ (Paper.Extension.Singleton.sumIso JoinedSeed Carry Carry).hom)
      (rankRow false)
    simp only [Bool.false_eq_true, ite_false, Functor.map_comp, Category.assoc] at eq
    have rep := congrArg (proj).map repeat_reset
    simp only [Functor.map_comp] at rep
    rw [← Category.assoc, repeatCover, reassoc_of% resultCover, ← Category.assoc next,
      show next ≫ _ = _ from rep]
    exact eq.trans (congrArg ((proj).map (baseRegion (phaseOut_typed false)) ≫ ·)
      (Paper.Extension.Singleton.sumCofan_inr_sumIso_hom JoinedSeed Carry Carry))
  · have eq := congrArg (fun f => (proj).map f ≫ (Paper.Extension.Singleton.sumIso JoinedSeed Carry Carry).hom)
      (rankRow true)
    simp only [Functor.map_comp, Category.assoc] at eq
    rw [← Category.assoc, resultCover]
    exact eq.trans (congrArg (out ≫ ·)
      (Paper.Extension.Singleton.sumCofan_inl_sumIso_hom JoinedSeed Carry Carry))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedCapturedRecurExit
