module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Reification.Iteration.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Thms

/-! The chosen iterator on an actual joined step emits a primitive request
on each pass. This loop has a typed empty result. -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot.ITree
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Paper.WithProjectionReturnsAndUnitEta (denoteITree denoteITree_tree)
open Paper.WithProjectionReturnsAndUnitEta.Reification (canonicalIterate)
open Paper.Extension.Singleton (ofType ofRegion sumIso iterateSum iterateSum_map)
open SyntacticCategory (iterationBody iterationDispatch iterateRegion iterateRegion_valueBranches)

private abbrev Atom := PEmpty.{2}

local instance : AtomValues Atom where
  carrier := PEmpty.elim

private inductive Op where
  | poll

private inductive Request : Type → Type where
  | poll : Request Bool

local instance : HasTy Op (Ty Atom) where
  src _ := .unit
  trg _ := .unit

local instance : HasEff Op Bool where
  eff _ := true

attribute [local instance] typeModel

local notation "Atoms" => AtomValues.carrier (κ := Atom)
local notation "TM" => ModelTree Request

local instance : InstructionModel Op (Ty Atom) Bool TM where
  denote _ _ := vis .poll (fun _ => pure PUnit.unit)
  denotePure f h := by cases h
  denote_pure f h := by cases h

private def raw : Primitive Request Op (Sigma Atoms) :=
  fun _ _ => vis .poll (fun _ => pure .unit)

set_option backward.isDefEq.respectTransparency false in
private theorem compatible :
    Compatible (κ' := Atom) ⟨fun f x => InstructionModel.denote
      (τ := Ty Atom) (ε := Bool) (m := TM) f x⟩ raw := by
  intro f x
  change raw f .unit = ((vis .poll (fun _ => pure PUnit.unit) : TM (Ty.denote Atoms .unit)) >>=
    fun y => pure (encodeValue Atoms .unit y))
  unfold raw
  rw [vis_bind]
  congr 1
  funext b
  change (pure .unit : TM (Value (Sigma Atoms))) =
    ((pure PUnit.unit : TM PUnit.{2}) >>= fun y : PUnit.{2} => pure (encodeValue Atoms .unit y))
  rw [pure_bind (m := TM)]
  rfl

private abbrev U : Ty Atom := .unit
private abbrev Z : Ty Atom := .empty
private abbrev JoinedSeed := Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Atom) (Φ := Op)
private abbrev Obj := ofType JoinedSeed

private def step : Region Op :=
  .let₁ (.op .poll .unit) (.br 0 (.inr .unit))

private theorem step_typed : ValueBranches [U] step [Silmaril.coprod Z U] :=
  .let₁ (.op .unit) (.br rfl (.inr .unit))

private noncomputable abbrev selected : Obj U ⟶ Obj Z :=
  canonicalIterate (ofRegion JoinedSeed step_typed ≫ (sumIso JoinedSeed Z U).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem selected_rep :
    selected = ofRegion JoinedSeed (iterateRegion_valueBranches step_typed) := by
  change iterateSum JoinedSeed ((ofRegion JoinedSeed step_typed ≫ (sumIso JoinedSeed Z U).hom) ≫
    (sumIso JoinedSeed Z U).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change iterateSum JoinedSeed
    ((Paper.WithProjectionReturnsAndUnitEta.projection).map (Paper.TypeCategory.ofRegion step_typed)) = _
  rw [iterateSum_map, Paper.TypeCategory.iterateSum_ofRegion]

private abbrev RawValue := Sigma Atoms
private abbrev RawState := BlockInput RawValue 1

private def enter : RawState := (⟨0, by decide⟩, .unit)

private def rawStep (_ : RawState) : TM (Transfer RawValue ⊕ RawState) :=
  vis .poll (fun _ => pure (Sum.inr enter))

private def modelStep (_ : PUnit.{2}) : TM (PEmpty.{2} ⊕ PUnit.{2}) :=
  InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TM) Op.poll PUnit.unit >>=
    fun _ => pure (Sum.inr PUnit.unit)

private theorem modelStep_eq (s : PUnit.{2}) :
    modelStep s = vis .poll (fun _ => pure (Sum.inr PUnit.unit)) := by
  change (vis Request.poll (fun _ => pure PUnit.unit) >>= fun _ => pure (Sum.inr PUnit.unit)) = _
  simp only [vis_bind, pure_bind (m := TM)]

private theorem step_image (s : PUnit.{2}) :
    denoteITree raw compatible (ofRegion JoinedSeed step_typed) s = modelStep s := by
  let encode : PEmpty.{2} ⊕ PUnit.{2} → TM (Transfer RawValue) :=
    fun b => pure (0, encodeValue Atoms (Silmaril.coprod Z U) b)
  let decode : Transfer RawValue → TM (PEmpty.{2} ⊕ PUnit.{2}) :=
    fun _ => pure (Sum.inr PUnit.unit)
  have inverse (b : PEmpty.{2} ⊕ PUnit.{2}) : (encode b >>= decode) = pure b := by
    rcases b with b | ⟨⟩
    · exact b.elim
    · exact pure_bind (m := TM) _ _
  have cancel (c : TM (PEmpty.{2} ⊕ PUnit.{2})) : ((c >>= encode) >>= decode) = c := by
    rw [bind_assoc, funext inverse]
    exact bind_pure _
  let env : Env RawValue := fun _ => .unit
  have encoded :
      (denoteITree raw compatible (ofRegion JoinedSeed step_typed) s >>= encode) =
        (modelStep s >>= encode) := by
    change (denoteITree raw compatible (ofRegion JoinedSeed step_typed) s >>= fun b =>
        pure (0, encodeValue Atoms (Silmaril.coprod Z U) b)) = _
    rw [denoteITree_tree raw compatible step_typed s env, modelStep_eq]
    simp only [step, encode, region, term, raw, vis_bind, pure_bind]
    rfl
  exact (cancel (denoteITree raw compatible (ofRegion JoinedSeed step_typed) s)).symm.trans
    ((congrArg (fun t : TM (Transfer RawValue) => t >>= decode) encoded).trans (cancel (modelStep s)))

private theorem rawBlock (env : Env RawValue) :
    region raw env ((iterationBody step).renameVars (Silmaril.DeBruijn.lift Nat.succ)) =
      vis .poll (fun _ => pure (0, .unit)) := by
  change region raw env (.let₁ (.op .poll .unit)
    (.case (.inr .unit) (.br 1 (.var 0)) (.br 0 (.var 0)))) = _
  simp only [region, term, raw, vis_bind, pure_bind, extend]

private theorem rawLoop (env : Env RawValue) :
    region raw (extend env .unit) (iterateRegion U step) = Silmaril.Elgot.iter rawStep enter := by
  have transfer : ∀ s : RawState,
      (region raw (extend (extend env .unit) s.2)
          ((iterationBody step).renameVars (Silmaril.DeBruijn.lift Nat.succ)) >>=
        fun exit => pure (splitTransfer 1 exit)) = rawStep s := by
    intro s
    rw [rawBlock]
    simp only [rawStep, vis_bind, pure_bind]
    rfl
  simp only [iterateRegion, feedbackRegion, cfgEntryContinuations, List.length_singleton, region, term,
    pure_bind, extend]
  change Silmaril.Elgot.iter (fun s : RawState =>
    region raw (extend (extend env .unit) s.2)
        ((iterationBody step).renameVars (Silmaril.DeBruijn.lift Nat.succ)) >>=
      fun exit => pure (splitTransfer 1 exit)) enter = _
  rw [funext transfer]

private def encodeExit (b : PEmpty.{2}) : TM (Transfer RawValue) :=
  pure (0, encodeValue Atoms Z b)

private theorem encodedModelLoop :
    (Silmaril.Elgot.iter modelStep PUnit.unit >>= encodeExit) = Silmaril.Elgot.iter rawStep enter := by
  let packed := Silmaril.Elgot.mapReturn modelStep encodeExit
  let packState : PUnit.{2} → RawState := fun _ => enter
  have commute :
      (packed >=> Silmaril.Elgot.liftPure (Sum.map id packState)) =
        (Silmaril.Elgot.liftPure packState >=> rawStep) := by
    funext s
    simp only [packed, Silmaril.Elgot.mapReturn, Bind.kleisliRight, Silmaril.Elgot.liftPure,
      Function.comp_apply, modelStep_eq, vis_bind, pure_bind (m := TM), Sum.elim_inr,
      Sum.map_inr, rawStep, packState]
  calc
    _ = Silmaril.Elgot.iter packed PUnit.unit :=
      congrFun (iterate_naturality modelStep encodeExit) PUnit.unit
    _ = _ := by
      simpa only [packState, Bind.kleisliRight, Silmaril.Elgot.liftPure, Function.comp_apply, pure_bind (m := TM)]
        using congrFun (iterate_uniformity packed rawStep packState commute) PUnit.unit

private theorem selected_image :
    denoteITree raw compatible selected PUnit.unit = Silmaril.Elgot.iter modelStep PUnit.unit := by
  let env : Env RawValue := fun _ => .unit
  have selectedEncoded : (denoteITree raw compatible selected PUnit.unit >>= encodeExit) =
      Silmaril.Elgot.iter rawStep enter := by
    rw [selected_rep]
    exact (denoteITree_tree raw compatible (iterateRegion_valueBranches step_typed) PUnit.unit env).trans
      (rawLoop env)
  let restore : Transfer RawValue → TM PEmpty.{2} := fun _ => diverge
  have restoreEmpty (c : TM PEmpty.{2}) : ((c >>= encodeExit) >>= restore) = c := by
    rw [bind_assoc, show (fun b => encodeExit b >>= restore) = pure from funext fun b => b.elim]
    exact bind_pure _
  have encoded :
      (denoteITree raw compatible selected PUnit.unit >>= encodeExit) =
        (Silmaril.Elgot.iter modelStep PUnit.unit >>= encodeExit) :=
    selectedEncoded.trans encodedModelLoop.symm
  have restored := congrArg (fun c : TM (Transfer RawValue) => c >>= restore) encoded
  exact (restoreEmpty (denoteITree raw compatible selected PUnit.unit)).symm.trans
    (restored.trans (restoreEmpty (Silmaril.Elgot.iter modelStep PUnit.unit)))

example :
    denoteITree raw compatible selected PUnit.unit =
      Silmaril.Elgot.iter (denoteITree raw compatible (ofRegion JoinedSeed step_typed)) PUnit.unit :=
  selected_image.trans (congrArg (fun f => Silmaril.Elgot.iter f PUnit.unit) (funext step_image)).symm

private theorem selected_observes_poll :
    out (denoteITree raw compatible selected PUnit.unit) =
      Part.some (.vis Request.poll (fun _ => denoteITree raw compatible selected PUnit.unit)) := by
  rw [selected_image]
  have unfoldStep : Silmaril.Elgot.iter modelStep PUnit.unit =
      vis Request.poll (fun _ => Silmaril.Elgot.iter modelStep PUnit.unit) := by
    simpa only [modelStep_eq, vis_bind, pure_bind (m := TM), Sum.elim_inr] using
      congrFun (iterate_fixpoint modelStep) PUnit.unit
  exact (congrArg out unfoldStep).trans (out_vis _ _)

example : denoteITree raw compatible selected PUnit.unit ≠ (diverge : TM PEmpty.{2}) := by
  intro same
  exact Part.some_ne_none _ (selected_observes_poll.symm.trans
    ((congrArg (fun t : TM PEmpty.{2} => out t) same).trans (out_diverge (E := Request) (A := PEmpty.{2}))))
