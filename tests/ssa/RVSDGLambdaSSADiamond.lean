module

import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Categorical.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Diamond.ExplicitRuntime.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.TwoExit.Model.Defs
import Silmaril.Raw.SSA.Isotope.Semantics.Model

namespace Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Tests

open CategoryTheory CategoryTheory.Limits
open Silmaril.Elgot
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ splitMapCoprod_coprodIsoSum)
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics
open LinearChain.Categorical (call choice)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Code := Silmaril.Ty Unit
private abbrev number : Code := .base ()
private abbrev pair : Code := .product number number
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)
private abbrev Runtime := StateT (List Nat) Part

private def coerce {A B : Code} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => coerce g ∘ coerce f
  | .product f g => fun (a, b) => (coerce f a, coerce g b)
  | .coprod f g => Sum.map (coerce f) (coerce g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Code where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := coerce

private inductive Op | header | classifier | left | right | join

local instance : HasTy Op Code :=
  ⟨(fun
    | .header => number
    | .classifier => number
    | .left => number
    | .right => pair
    | .join => pair),
    (fun
    | .header => .coprod number number
    | .classifier => .coprod number pair
    | .left => pair
    | .right => pair
    | .join => .coprod pair number)⟩

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .header, a => StateT.mk fun state =>
    let n : Nat := a
    Part.some (if n == 0 then .inl state.length else .inr n, state ++ [1])
  | .classifier, b => StateT.mk fun state =>
    let n : Nat := b
    Part.some (if n == 3 then .inr (n, state.length) else .inl n, state ++ [2])
  | .left, x => StateT.mk fun state => Part.some ((x, state.length), state ++ [3])
  | .right, (x, captured) => StateT.mk fun state =>
    let n : Nat := x
    let seen : Nat := captured
    if state.head? == some 9 then Part.some ((n + seen, state.length), state ++ [5]) else Part.none
  | .join, (x, captured) => StateT.mk fun state =>
    let n : Nat := x
    Part.some (if n == 1 then .inr (0 : Nat) else .inl (captured, state.length), state ++ [4])

local instance : InstructionModel Op Code Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private def spec : Blocks Op number number number pair pair number pair :=
  ⟨⟨.header, rfl, rfl⟩, ⟨⟨.classifier, rfl, rfl⟩, ⟨.left, rfl, rfl⟩, ⟨.right, rfl, rfl⟩⟩,
    ⟨.join, rfl, rfl⟩⟩

local notation "J" => typeJ (m := Runtime)
local notation "M" => Isotope.LambdaSSA.Semantics.Categorical.ofMonadicTypeModel (τ := Code)

noncomputable local instance : Isotope.LetIter.Semantics.Categorical.InstructionModel J M Op :=
  Isotope.LambdaSSA.Semantics.Categorical.ofMonadicInstructionModel (ε := Bool)

private noncomputable def readChoice (U V : Type) :
    (J).obj U ⨿ (J).obj V ⟶ (J).obj (U ⊕ V) :=
  (Kleisli.Type.coprodIsoSum Runtime ((J).obj U) ((J).obj V)).hom

private theorem comp_apply {U V W : Type}
    (f : (J).obj U ⟶ (J).obj V) (g : (J).obj V ⟶ (J).obj W) (a : U) :
    (f ≫ g).of a = (f.of a >>= g.of : Runtime W) :=
  congrFun (Kleisli.Type.comp_of_eq_kleisliRight Runtime f g) a

private theorem map_apply {U V : Type} (f : U ⟶ V) (a : U) :
    ((J).map f).of a = (pure (f a) : Runtime V) := rfl

private theorem call_apply {A B : Code} (p : TwoBlock.Instruction Op A B) (a : Value A) :
    (call J M p).of a = TwoBlock.call (ε := Bool) (m := Runtime) p a := by
  obtain ⟨op, src, dst⟩ := p
  subst A
  subst B
  simp [call, TwoBlock.call]
  rfl

private theorem choice_apply {A L R : Code}
    (p : TwoBlock.Instruction Op A (Silmaril.coprod L R)) (a : Value A) :
    (choice J M p ≫ readChoice (Value L) (Value R)).of a =
      callCase (ε := Bool) (m := Runtime) p a := by
  let U := (M).obj L
  let V := (M).obj R
  change (choice J M p ≫ readChoice U V).of a = _
  unfold choice readChoice
  simp only [Category.assoc]
  rw [splitMapCoprod_coprodIsoSum (m := Runtime) U V, ← (J).map_comp, comp_apply, call_apply]
  unfold callCase
  congr 1
  funext x
  rw [map_apply]
  congr 1
  exact Agreement.coprod_hom_agrees L R x

private theorem branch_apply {A L R : Code} {O : Type}
    (p : TwoBlock.Instruction Op A (Silmaril.coprod L R))
    (l : (J).obj (Value L) ⟶ (J).obj O) (r : (J).obj (Value R) ⟶ (J).obj O) (a : Value A) :
    (choice J M p ≫ coprod.desc l r).of a =
      (callCase (ε := Bool) (m := Runtime) p a >>= Sum.elim l.of r.of) := by
  rw [← Kleisli.Type.coprodIsoSum_hom_sumElim, ← Category.assoc, comp_apply]
  change (show Runtime (Value L ⊕ Value R) from
    (choice J M p ≫ readChoice (Value L) (Value R)).of a) >>= Sum.elim l.of r.of = _
  rw [choice_apply]

private theorem diamond_apply (b : Nat) :
    (Categorical.diamond J M spec.diamond).of b =
      (callCase (ε := Bool) (m := Runtime) spec.diamond.classifier b >>= fun result =>
        Sum.elim (TwoBlock.call (ε := Bool) spec.diamond.left)
          (TwoBlock.call (ε := Bool) spec.diamond.right) result) := by
  unfold Categorical.diamond
  rw [branch_apply]
  congr 1
  funext result
  cases result with
  | inl x => exact call_apply spec.diamond.left x
  | inr y => exact call_apply spec.diamond.right y

private noncomputable def diamondThenJoin (b : Nat) :
    Runtime ((Nat × Nat) ⊕ Nat) :=
  ((Categorical.diamond J M spec.diamond ≫ choice J M spec.join) ≫
    readChoice (Value pair) (Value number)).of b

private theorem diamondThenJoin_apply (b : Nat) :
    diamondThenJoin b =
      (callCase (ε := Bool) (m := Runtime) spec.diamond.classifier b >>= fun result => do
        let k ← Sum.elim (TwoBlock.call (ε := Bool) spec.diamond.left)
          (TwoBlock.call (ε := Bool) spec.diamond.right) result
        callCase (ε := Bool) spec.join k) := by
  simp only [diamondThenJoin, Category.assoc, comp_apply (Categorical.diamond J M spec.diamond),
    diamond_apply, bind_assoc]
  congr 1
  funext result
  congr 1
  funext k
  exact choice_apply spec.join k

-- The caller has already appended the header marker. The classifier appends
-- 2, the selected left block reads length 2 and appends 3, and the join reads
-- length 3 and appends 4. The undefined right block is skipped.
private theorem leftRun : (diamondThenJoin 2).run [1] = Part.some (.inl (2, 3), [1, 2, 3, 4]) := by
  rw [diamondThenJoin_apply]
  simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change ((TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.left (2 : Nat)).run [1, 2]).bind _ = _
  have left : (TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.left (2 : Nat)).run [1, 2] =
      Part.some (((2 : Nat), (2 : Nat)), [1, 2, 3]) := by
    simp [TwoBlock.call, spec, InstructionModel.denote, instruction]
  rw [left, Part.bind_some]
  rfl

private theorem rightRun : (diamondThenJoin 3).run [1] = Part.none := by
  rw [diamondThenJoin_apply]
  simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change ((TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.right ((3 : Nat), (1 : Nat))).run [1, 2]).bind _ = _
  have right : (TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.right ((3 : Nat), (1 : Nat))).run [1, 2] =
      Part.none := by
    simp [TwoBlock.call, spec, InstructionModel.denote, instruction]
  rw [right, Part.bind_none]

private theorem feedbackRun : (diamondThenJoin 1).run [1] = Part.some (.inr 0, [1, 2, 3, 4]) := by
  rw [diamondThenJoin_apply]
  simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change ((TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.left (1 : Nat)).run [1, 2]).bind _ = _
  have left : (TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.left (1 : Nat)).run [1, 2] =
      Part.some (((1 : Nat), (2 : Nat)), [1, 2, 3]) := by
    simp [TwoBlock.call, spec, InstructionModel.denote, instruction]
  rw [left, Part.bind_some]
  rfl

private noncomputable abbrev ExitLabels := CategoricalLabelDen [number, pair]

private noncomputable def headerLabel : Nat ⟶ ExitLabels :=
  Isotope.LambdaSSA.Semantics.Categorical.labelInject M (L := [number, pair]) 0 rfl

private noncomputable def bodyLabel : Nat × Nat ⟶ ExitLabels :=
  Isotope.LambdaSSA.Semantics.Categorical.labelInject M (L := [number, pair]) 1 rfl

@[reassoc] private theorem read_inl (U V : Type) :
    (coprod.inl : (J).obj U ⟶ (J).obj U ⨿ (J).obj V) ≫ readChoice U V =
      (J).map (TypeCat.ofHom Sum.inl) := by
  rw [readChoice, Kleisli.Type.inl_coprodIsoSum_hom]
  rfl

@[reassoc] private theorem read_inr (U V : Type) :
    (coprod.inr : (J).obj V ⟶ (J).obj U ⨿ (J).obj V) ≫ readChoice U V =
      (J).map (TypeCat.ofHom Sum.inr) := by
  rw [readChoice, Kleisli.Type.inr_coprodIsoSum_hom]
  rfl

private theorem map_read {U V W : Type} (f : U ⟶ W) :
    coprod.map ((J).map f) (𝟙 ((J).obj V)) ≫ readChoice W V =
      readChoice U V ≫ (J).map (TypeCat.ofHom (Sum.map f id)) := by
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, read_inl_assoc, read_inl, ← CategoryTheory.Functor.map_comp]
    rfl
  · simp only [coprod.inr_map_assoc, Category.id_comp, read_inr_assoc, read_inr,
      ← CategoryTheory.Functor.map_comp]
    rfl

private noncomputable def round (a : Nat) : Runtime (ExitLabels ⊕ Nat) :=
  (Categorical.activation J M spec ≫ readChoice ExitLabels Nat).of a

private theorem round_apply (a : Nat) : round a =
    (callCase (ε := Bool) (m := Runtime) spec.header a >>= fun
      | .inl e => pure (.inl (headerLabel e))
      | .inr b => diamondThenJoin b >>= fun res => pure (Sum.map bodyLabel id res)) := by
  unfold round Categorical.activation
  rw [Category.assoc, coprod.desc_comp, branch_apply]
  congr 1
  funext result
  cases result with
  | inl e =>
    change (((J).map headerLabel ≫ coprod.inl) ≫ readChoice ExitLabels Nat).of e = _
    rw [Category.assoc, read_inl, ← CategoryTheory.Functor.map_comp, map_apply]
    rfl
  | inr b =>
    change ((Categorical.diamond J M spec.diamond ≫ choice J M spec.join ≫
        coprod.map ((J).map bodyLabel) (𝟙 ((J).obj Nat))) ≫ readChoice ExitLabels Nat).of b = _
    rw [Category.assoc, Category.assoc, map_read, ← Category.assoc, ← Category.assoc, comp_apply]
    change diamondThenJoin b >>= (fun r => (pure (Sum.map bodyLabel id r) : Runtime _)) = _
    rfl

private noncomputable def observe (a : Nat) : Runtime ExitLabels :=
  (Categorical.denoteForm J M (Form.loop spec)).of (Agreement.envToCategorical (PUnit.unit, a))

private theorem observe_iter (a : Nat) : observe a = iter round a := by
  unfold observe Categorical.denoteForm Categorical.denote
  rw [comp_apply]
  change ((pure a : Runtime Nat) >>= _) = _
  rw [pure_bind]
  exact congrFun (Kleisli.Type.iterate_of Runtime (Categorical.activation J M spec)) a

private theorem headerStep (a : Nat) (hn : a ≠ 0) :
    (callCase (ε := Bool) (m := Runtime) spec.header a).run [] = Part.some (.inr a, [1]) := by
  simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    TypeModel.coprodEquiv, hn]
  rfl

private theorem bodyExitStep :
    Silmaril.Elgot.StateT.body round (2, []) = Part.some (.inl (bodyLabel (2, 3), [1, 2, 3, 4])) := by
  have hd := headerStep 2 (by decide)
  simp only [Silmaril.Elgot.StateT.body, round_apply, StateT.run_bind,
    Part.bind_eq_bind, hd, Part.bind_some, leftRun, StateT.run_pure, Part.pure_eq_some]
  rfl

example : (observe 2).run [] = Part.some (bodyLabel (2, 3), [1, 2, 3, 4]) := by
  rw [observe_iter, Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done (by rw [bodyExitStep]; exact Part.mem_some_iff.mpr rfl)

-- The join can return to the header. The next header sees all prior
-- effects and exits without entering the diamond again.
example : (observe 1).run [] = Part.some (headerLabel 4, [1, 2, 3, 4, 1]) := by
  have back : Silmaril.Elgot.StateT.body round (1, []) = Part.some (.inr (0, [1, 2, 3, 4])) := by
    have hd := headerStep 1 (by decide)
    simp only [Silmaril.Elgot.StateT.body, round_apply, StateT.run_bind, Part.bind_eq_bind, hd,
      Part.bind_some, feedbackRun, StateT.run_pure, Part.pure_eq_some]
    rfl
  have last : Silmaril.Elgot.StateT.body round (0, [1, 2, 3, 4]) =
      Part.some (.inl (headerLabel 4, [1, 2, 3, 4, 1])) := by
    have hd : (callCase (ε := Bool) (m := Runtime) spec.header (0 : Nat)).run [1, 2, 3, 4] =
        Part.some (.inl (4 : Nat), [1, 2, 3, 4, 1]) := by
      simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction, TypeModel.coprodEquiv]
      rfl
    simp only [Silmaril.Elgot.StateT.body, round_apply, StateT.run_bind, Part.bind_eq_bind,
      hd, Part.bind_some, StateT.run_pure, Part.pure_eq_some]
    rfl
  rw [observe_iter, Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more (by rw [back]; exact Part.mem_some_iff.mpr rfl)
    (.done (by rw [last]; exact Part.mem_some_iff.mpr rfl))

example : (observe 3).run [] = Part.none := by
  have step : Silmaril.Elgot.StateT.body round (3, []) = Part.none := by
    have hd := headerStep 3 (by decide)
    simp only [Silmaril.Elgot.StateT.body, round_apply, StateT.run_bind,
      Part.bind_eq_bind, hd, Part.bind_some, rightRun, Part.bind_none]
  rw [observe_iter, Silmaril.Elgot.StateT.run_iter, Part.eq_none_iff]
  intro out run
  rw [Silmaril.Elgot.Part.mem_iter_iff] at run
  cases run with
  | done h => simp [step] at h
  | more h _ => simp [step] at h

example (coherent : Agreement.RegionCoherent (τ := Code) (Φ := Op) (ε := Bool) (m := Runtime)) :
    ((Agreement.categoricalRegionDenote (ε := Bool) (m := Runtime) (regionTyping spec)).of
      (Agreement.envToCategorical (PUnit.unit, (2 : Nat)))).run [] =
        Part.some (bodyLabel (2, 3), [1, 2, 3, 4]) := by
  let _ : Isotope.LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := Op) J M := coherent
  rw [Agreement.categoricalRegionDenote, Categorical.denoteRegion_eq J M spec]
  change (observe 2).run [] = _
  rw [observe_iter, Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done (by rw [bodyExitStep]; exact Part.mem_some_iff.mpr rfl)

private def lowered := ExplicitRuntime.lower (ExplicitRuntime.SSAForm.loop spec)
private def raised := ExplicitRuntime.raise (ExplicitRuntime.RVForm.loop spec)

example : lowered.1 = ExplicitRuntime.graph spec := rfl
example : raised.1 = region spec := rfl

private def stateRound : Nat → Runtime (LabelDen [number,pair] ⊕ Nat) :=
  ExplicitRuntime.round (ε := Bool) spec

private theorem sharedBody (b : Nat) : ExplicitRuntime.bodyAction (ε := Bool) spec b = diamondThenJoin b :=
  (diamondThenJoin_apply b).symm

private def leftExit : LabelDen [number,pair] := .inr (.inl ((2 : Nat), (3 : Nat)))
private def rightExit : LabelDen [number,pair] := .inr (.inl ((3 : Nat), (4 : Nat)))
private def headerExit : LabelDen [number,pair] := .inl (4 : Nat)

private theorem leftStep :
    Silmaril.Elgot.StateT.body stateRound (2, []) = Part.some (.inl (leftExit, [1, 2, 3, 4])) := by
  have hd := headerStep 2 (by decide)
  simp only [Silmaril.Elgot.StateT.body, stateRound, ExplicitRuntime.round, StateT.run_bind, Part.bind_eq_bind,
    hd, Part.bind_some, sharedBody]
  rw [leftRun, Part.bind_some]
  simp only [StateT.run_pure, Part.pure_eq_some, Part.bind_some]
  rfl

-- The pair-typed right arm is defined with the leading marker 9. It sees
-- the classifier's token, appends 5, and delivers a pair to the same join.
private theorem rightSuccess : (diamondThenJoin 3).run [9, 1] =
    Part.some (.inl (3, 4), [9, 1, 2, 5, 4]) := by
  rw [diamondThenJoin_apply]
  simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction,
    TypeModel.coprodEquiv, StateT.run_bind, Part.bind_eq_bind, Part.bind_some]
  change ((TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.right ((3 : Nat), (2 : Nat))).run
      [9, 1, 2]).bind _ = _
  have arm : (TwoBlock.call (ε := Bool) (m := Runtime) spec.diamond.right ((3 : Nat), (2 : Nat))).run
      [9, 1, 2] = Part.some (((5 : Nat), (3 : Nat)), [9, 1, 2, 5]) := by
    simp [TwoBlock.call, spec, InstructionModel.denote, instruction]
  rw [arm, Part.bind_some]
  rfl

private theorem rightStep :
    Silmaril.Elgot.StateT.body stateRound (3, [9]) = Part.some (.inl (rightExit, [9, 1, 2, 5, 4])) := by
  have hd : (callCase (ε := Bool) (m := Runtime) spec.header (3 : Nat)).run [9] =
      Part.some (.inr (3 : Nat), [9, 1]) := by
    simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction, TypeModel.coprodEquiv]
    rfl
  simp only [Silmaril.Elgot.StateT.body, stateRound, ExplicitRuntime.round, StateT.run_bind, Part.bind_eq_bind,
    hd, Part.bind_some, sharedBody]
  rw [rightSuccess, Part.bind_some]
  simp only [StateT.run_pure, Part.pure_eq_some, Part.bind_some]
  rfl

private theorem feedbackStep :
    Silmaril.Elgot.StateT.body stateRound (1, []) = Part.some (.inr (0, [1, 2, 3, 4])) := by
  have hd := headerStep 1 (by decide)
  simp only [Silmaril.Elgot.StateT.body, stateRound, ExplicitRuntime.round, StateT.run_bind, Part.bind_eq_bind,
    hd, Part.bind_some, sharedBody]
  rw [feedbackRun, Part.bind_some]
  simp only [StateT.run_pure, Part.pure_eq_some, Part.bind_some]
  rfl

private theorem doneStep :
    Silmaril.Elgot.StateT.body stateRound (0, [1, 2, 3, 4]) =
      Part.some (.inl (headerExit, [1, 2, 3, 4, 1])) := by
  have hd : (callCase (ε := Bool) (m := Runtime) spec.header (0 : Nat)).run [1, 2, 3, 4] =
      Part.some (.inl (4 : Nat), [1, 2, 3, 4, 1]) := by
    simp [callCase, TwoBlock.call, spec, InstructionModel.denote, instruction, TypeModel.coprodEquiv]
    rfl
  simp only [Silmaril.Elgot.StateT.body, stateRound, ExplicitRuntime.round, StateT.run_bind, Part.bind_eq_bind,
    hd, Part.bind_some, StateT.run_pure, Part.pure_eq_some]
  rfl

private theorem leftWire : ExplicitRuntime.returns (ε := Bool) lowered.1 (2 : Nat) [] leftExit [1, 2, 3, 4] := by
  apply (lowered.2.returns_iff (ε := Bool) (2 : Nat) leftExit [] [1, 2, 3, 4]).mp
  change (iter stateRound 2).run [] = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done (by rw [leftStep]; exact Part.mem_some_iff.mpr rfl)

private theorem rightWire :
    ExplicitRuntime.returns (ε := Bool) lowered.1 (3 : Nat) [9] rightExit [9, 1, 2, 5, 4] := by
  apply (lowered.2.returns_iff (ε := Bool) (3 : Nat) rightExit [9] [9, 1, 2, 5, 4]).mp
  change (iter stateRound 3).run [9] = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .done (by rw [rightStep]; exact Part.mem_some_iff.mpr rfl)

example : ExplicitRuntime.returns (ε := Bool) lowered.1 (1 : Nat) [] headerExit [1, 2, 3, 4, 1] := by
  apply (lowered.2.returns_iff (ε := Bool) (1 : Nat) headerExit [] [1, 2, 3, 4, 1]).mp
  change (iter stateRound 1).run [] = _
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff]
  exact .more (by rw [feedbackStep]; exact Part.mem_some_iff.mpr rfl)
    (.done (by rw [doneStep]; exact Part.mem_some_iff.mpr rfl))

private theorem undefinedWire (label : LabelDen [number,pair]) (token : List Nat) :
    ¬ ExplicitRuntime.returns (ε := Bool) lowered.1 (3 : Nat) [] label token := by
  intro h
  have step : Silmaril.Elgot.StateT.body stateRound (3, []) = Part.none := by
    have hd := headerStep 3 (by decide)
    simp only [Silmaril.Elgot.StateT.body, stateRound, ExplicitRuntime.round, StateT.run_bind, Part.bind_eq_bind,
      hd, Part.bind_some, sharedBody]
    rw [rightRun, Part.bind_none, Part.bind_none]
  have observed := (lowered.2.returns_iff (ε := Bool) (3 : Nat) label [] token).mpr h
  change (iter stateRound 3).run [] = _ at observed
  rw [Silmaril.Elgot.StateT.run_iter, Part.eq_some_iff, Silmaril.Elgot.Part.mem_iter_iff] at observed
  cases observed with
  | done first => simp [step] at first
  | more first _ => simp [step] at first

private abbrev Coherent := Agreement.RegionCoherent (τ := Code) (Φ := Op) (ε := Bool) (m := Runtime)

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (2 : Nat))).run [] =
      Part.some (leftExit, [1, 2, 3, 4]) :=
  (lowered.2.region_returns_iff coherent (PUnit.unit, (2 : Nat)) leftExit [] [1, 2, 3, 4]).mpr leftWire

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) raised.2.typing (PUnit.unit, (3 : Nat))).run [9] =
      Part.some (rightExit, [9, 1, 2, 5, 4]) :=
  (raised.2.region_returns_iff coherent (PUnit.unit, (3 : Nat)) rightExit [9] [9, 1, 2, 5, 4]).mpr rightWire

example (coherent : Coherent) (label : LabelDen [number,pair]) (token : List Nat) :
    (Region.denote (ε := Bool) (m := Runtime) lowered.2.typing (PUnit.unit, (3 : Nat))).run [] ≠
      Part.some (label, token) := fun returned =>
  undefinedWire label token
    ((lowered.2.region_returns_iff coherent (PUnit.unit, (3 : Nat)) label [] token).mp returned)

end Silmaril.SSA.RVSDG.LambdaSSA.Diamond.Tests
