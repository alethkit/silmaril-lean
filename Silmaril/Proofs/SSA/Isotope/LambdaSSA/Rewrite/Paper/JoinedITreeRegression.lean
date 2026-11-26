module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Denotation.ITree.Iteration.Thms

/-! The chosen iterator preserves an empty-exit polling loop and a two-phase
polling loop that repeats once before returning a tagged result. -/

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot.ITree
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Paper.WithProjectionReturnsAndUnitEta (denoteITree denoteITree_tree denoteITree_canonicalIterate)
open Paper.WithProjectionReturnsAndUnitEta.Reification (canonicalIterate)
open Paper.Extension.Singleton (ofType ofRegion sumIso projectStep projectStep_comp_sumIso_inv)

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

private noncomputable def chosen {A B : Ty Atom} (f : Obj A ⟶ Obj (Silmaril.coprod B A)) :
    Obj A ⟶ Obj B ⨿ Obj A :=
  f ≫ (sumIso JoinedSeed B A).hom

set_option backward.isDefEq.respectTransparency false in
private theorem chosen_normalize {A B : Ty Atom} (f : Obj A ⟶ Obj (Silmaril.coprod B A)) :
    chosen f ≫ (sumIso JoinedSeed B A).inv = f := by
  simp only [chosen, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private noncomputable abbrev selected : Obj U ⟶ Obj Z :=
  canonicalIterate (chosen (ofRegion JoinedSeed step_typed))

private abbrev RawValue := Sigma Atoms

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

set_option backward.isDefEq.respectTransparency false in
private theorem selected_image :
    denoteITree raw compatible selected PUnit.unit = Silmaril.Elgot.iter modelStep PUnit.unit := by
  have agree := denoteITree_canonicalIterate raw compatible (chosen (ofRegion JoinedSeed step_typed)) PUnit.unit
  rw [chosen_normalize, funext step_image] at agree
  exact agree

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

private abbrev Phase := Ty.coprod U U
private abbrev PhaseValue := PUnit.{2} ⊕ PUnit.{2}

private def phaseBody : Region Op :=
  .let₁ (.op .poll .unit)
    (.case (.var 1) (.br 0 (.inr (.inr .unit))) (.br 0 (.inl (.inr .unit))))

private theorem phaseBody_typed : ValueBranches [Phase] phaseBody [Silmaril.coprod Phase Phase] :=
  .let₁ (.op .unit) (.case (.var (i := 1) rfl)
    (.br rfl (.inr (.inr .unit))) (.br rfl (.inl (.inr .unit))))

private def phaseStep (s : PhaseValue) : TM (PhaseValue ⊕ PhaseValue) :=
  vis .poll fun _ => pure (match s with
    | .inl _ => .inr (.inr PUnit.unit)
    | .inr _ => .inl (.inr PUnit.unit))

set_option backward.isDefEq.respectTransparency false in
private theorem phaseStep_image (s : PhaseValue) :
    denoteITree raw compatible (ofRegion JoinedSeed phaseBody_typed) s = phaseStep s := by
  let encode : PhaseValue ⊕ PhaseValue → TM (Transfer RawValue) :=
    fun b => pure (0, encodeValue Atoms (Silmaril.coprod Phase Phase) b)
  let decode : Transfer RawValue → TM (PhaseValue ⊕ PhaseValue) := fun p => pure
    (match p.2 with
     | .inr (.inr _) => .inr (.inr PUnit.unit)
     | .inr _ => .inr (.inl PUnit.unit)
     | .inl (.inr _) => .inl (.inr PUnit.unit)
     | _ => .inl (.inl PUnit.unit))
  have inverse (b : PhaseValue ⊕ PhaseValue) : (encode b >>= decode) = pure b := by
    rcases b with (⟨⟩ | ⟨⟩) | (⟨⟩ | ⟨⟩) <;> exact pure_bind (m := TM) _ _
  have cancel (c : TM (PhaseValue ⊕ PhaseValue)) : ((c >>= encode) >>= decode) = c := by
    rw [bind_assoc, funext inverse]
    exact bind_pure _
  let env : Env RawValue := fun _ => .unit
  have encoded :
      (denoteITree raw compatible (ofRegion JoinedSeed phaseBody_typed) s >>= encode) =
        (phaseStep s >>= encode) := by
    change (denoteITree raw compatible (ofRegion JoinedSeed phaseBody_typed) s >>= fun b =>
      pure (0, encodeValue Atoms (Silmaril.coprod Phase Phase) b)) = _
    rw [denoteITree_tree raw compatible phaseBody_typed s env]
    rcases s with ⟨⟩ | ⟨⟩ <;> (
      simp only [phaseBody, phaseStep, encode, region, term, raw, vis_bind, pure_bind,
        extend, encodeValue]; rfl)
  exact (cancel (denoteITree raw compatible (ofRegion JoinedSeed phaseBody_typed) s)).symm.trans
    ((congrArg (fun t : TM (Transfer RawValue) => t >>= decode) encoded).trans (cancel (phaseStep s)))

private noncomputable def phaseChosen : Obj Phase ⟶ Obj Phase ⨿ Obj Phase :=
  projectStep JoinedSeed (Paper.TypeCategory.ofRegion phaseBody_typed ≫
    (Paper.TypeCategory.sumIso Phase Phase).hom)

set_option backward.isDefEq.respectTransparency false in
private theorem phaseSelected_image (s : PhaseValue) :
    denoteITree raw compatible (canonicalIterate phaseChosen) s = Silmaril.Elgot.iter phaseStep s := by
  have agree := denoteITree_canonicalIterate raw compatible phaseChosen s
  rw [phaseChosen, projectStep_comp_sumIso_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id] at agree
  change _ = Silmaril.Elgot.iter (denoteITree raw compatible (ofRegion JoinedSeed phaseBody_typed)) s at agree
  rw [funext phaseStep_image] at agree
  exact agree

example :
    denoteITree raw compatible (canonicalIterate phaseChosen) (Sum.inl PUnit.unit) =
      vis Request.poll (fun _ => vis Request.poll (fun _ => pure (Sum.inr PUnit.unit))) := by
  refine (phaseSelected_image (Sum.inl PUnit.unit)).trans ?_
  have firstPoll : Silmaril.Elgot.iter phaseStep (Sum.inl PUnit.unit) =
      vis Request.poll (fun _ => Silmaril.Elgot.iter phaseStep (Sum.inr PUnit.unit)) := by
    simpa only [phaseStep, vis_bind, pure_bind (m := TM), Sum.elim_inr] using
      congrFun (iterate_fixpoint phaseStep) (Sum.inl PUnit.unit)
  have secondPoll : Silmaril.Elgot.iter phaseStep (Sum.inr PUnit.unit) =
      vis Request.poll (fun _ => pure (Sum.inr PUnit.unit)) := by
    simpa only [phaseStep, vis_bind, pure_bind (m := TM), Sum.elim_inl] using
      congrFun (iterate_fixpoint phaseStep) (Sum.inr PUnit.unit)
  rw [firstPoll, secondPoll]
  rfl
