module

import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Thms
import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
import Silmaril.Raw.SSA.Isotope.Semantics.Model
meta import Silmaril.SSA.Isotope.Types.Defs
meta import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Tests

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)
open TwoBlock.TwoExit (callCase)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private abbrev Ty := Silmaril.Ty Unit
private abbrev number : Ty := .base ()
private abbrev unitTy : Ty := .unit
private abbrev Value := Silmaril.Ty.denote (fun _ : Unit => Nat)
private abbrev Runtime := StateT Nat Part

private inductive Op | header | finalHeader | selectExit | body | maybeBody | join
  deriving DecidableEq

local instance : HasTy Op Ty :=
  ⟨fun _ => number, fun
    | .header | .join => .coprod number number
    | .finalHeader | .selectExit => .coprod unitTy number
    | .body | .maybeBody => number⟩

private def valueCoe {A B : Ty} : Isotope.Ty.Subty A B → Value A → Value B
  | .refl _ => id
  | .trans f g => valueCoe g ∘ valueCoe f
  | .product f g => fun (a, b) => (valueCoe f a, valueCoe g b)
  | .coprod f g => Sum.map (valueCoe f) (valueCoe g)
  | .empty _ => PEmpty.elim
  | .unit _ => fun _ => PUnit.unit

local instance : TypeModel Ty where
  interp := Value
  productEquiv _ _ := Equiv.refl _
  unitEquiv := ⟨fun _ => (), fun _ => PUnit.unit, fun x => by cases x; rfl, fun x => by cases x; rfl⟩
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := ⟨PEmpty.elim, Empty.elim, fun x => PEmpty.elim x, fun x => Empty.elim x⟩
  coe := valueCoe

local instance : HasEff Op Bool := ⟨fun _ => true⟩

private def instruction : (op : Op) → Value (instrSrc op) → Runtime (Value (instrTrg op))
  | .header, input => StateT.mk fun token => Part.some (.inr input, token + 1)
  | .finalHeader, input => StateT.mk fun token => Part.some (.inr input, token + 1)
  | .selectExit, input => StateT.mk fun token =>
    Part.some (if (show Nat from input) = 0 then .inl PUnit.unit else .inr input, token + 1)
  | .body, input => StateT.mk fun token => Part.some ((show Nat from input) + token, token + 1)
  | .maybeBody, input => StateT.mk fun token =>
    if (show Nat from input) = 9 then Part.none else Part.some ((show Nat from input) + token, token + 1)
  | .join, input => StateT.mk fun token =>
    Part.some (if token = 2 then .inr input else .inl input, token + 1)

local instance : InstructionModel Op Ty Bool Runtime where
  denote := instruction
  denotePure _ h := False.elim (by change true = false at h; cases h)
  denote_pure _ h _ := False.elim (by change true = false at h; cases h)

private theorem call_run {X Y : Ty} (p : TwoBlock.Instruction Op X Y) (input : Value X) :
    TwoBlock.call (ε := Bool) (m := Runtime) p input =
      p.output ▸ instruction p.op (p.input.symm ▸ input) := by
  obtain ⟨op, src, dst⟩ := p
  subst X
  subst Y
  unfold TwoBlock.call
  change instruction op input >>= pure = instruction op input
  exact bind_pure _

private theorem callCase_run {X L R : Ty} (p : TwoBlock.Instruction Op X (Silmaril.coprod L R))
    (input : Value X) :
    callCase (ε := Bool) (m := Runtime) p input =
      (show Runtime (Value (Silmaril.coprod L R)) from p.output ▸ instruction p.op (p.input.symm ▸ input)) := by
  unfold callCase
  rw [call_run]
  change (_ : Runtime (Value L ⊕ Value R)) >>= pure = _
  exact bind_pure _

private def stepLoop : Loop Op number number number number number :=
  ⟨⟨.header, rfl, rfl⟩, .instruction ⟨.body, rfl, rfl⟩, ⟨.join, rfl, rfl⟩⟩

private def finalLoop : Loop Op number number number unitTy number :=
  ⟨⟨.finalHeader, rfl, rfl⟩, stepLoop.body, stepLoop.join⟩

private def stage := Spine.loop stepLoop
private def finalStage := Spine.loop finalLoop
private def firstTwo := Spine.link stage stage
private def pipeline := Spine.link firstTwo finalStage

private def firstCut : Cut stage.code stage.code firstTwo.graph := ⟨rfl⟩
private def secondCut : Cut firstTwo.code finalStage.code pipeline.graph := ⟨rfl⟩

example : certifyCut stage.code stage.code firstTwo.graph = some firstCut := firstCut.certified
example : certifyCut firstTwo.code finalStage.code pipeline.graph = some secondCut := secondCut.certified

private def prefixDecomposition : Decomposition firstTwo.graph :=
  Decomposition.link stage.decomposition stage.decomposition firstCut

private def recovered : Decomposition pipeline.graph :=
  Decomposition.link prefixDecomposition finalStage.decomposition secondCut

example : recovered.recover = Flat.link (Flat.link (.loop stepLoop) (.loop stepLoop)) (.loop finalLoop) := rfl

example : (Spine.ofLoop (ExplicitRuntime.Reverse.canonical stepLoop)).source = stage.source := by
  rw [Spine.ofLoop, ExplicitRuntime.Reverse.canonical_decode]
  rfl

private theorem pipelineForm : Recognize.LeftAssociated pipeline :=
  .push finalLoop (.push stepLoop (.single stepLoop (.instruction _)) (.instruction _)) (.instruction _)

private theorem pipelineRecognized : Recognize.recognize pipeline.graph = some recovered :=
  Recognize.complete pipeline pipelineForm

private def nestedLoop : Loop Op number number number number number :=
  { stepLoop with
    body := .sequence
      (.choice stepLoop.header stepLoop.body (.sequence stepLoop.body stepLoop.body))
      stepLoop.body }

private def nestedPipeline := Spine.link stage (.loop nestedLoop)

example : Recognize.recognize nestedPipeline.graph = some nestedPipeline.decomposition :=
  Recognize.complete nestedPipeline (.push nestedLoop (.single stepLoop (.instruction _))
    (.thenChoice stepLoop.header (.instruction _) (.thenInstruction _ (.instruction _)) (.instruction _)))

private def exit (n : Nat) : LabelDen [number,number] := .inr (.inl n)
private def finalExit : LabelDen [unitTy,number] := .inr (.inl (23 : Nat))

private theorem firstRun :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) stepLoop) (1 : Nat)).run (0 : Nat) = Part.some (exit 6, 6) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  refine .more (a' := ((2 : Nat), 3)) ?_ (.done ?_)
  all_goals
    simp [Elgot.StateT.body, ExplicitRuntime.round, stepLoop, ExplicitRuntime.bodyAction,
      callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
      Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, exit]

private theorem secondRun :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) stepLoop) (6 : Nat)).run (6 : Nat) = Part.some (exit 13, 9) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, stepLoop, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, exit]

private theorem finalRun :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) finalLoop) (13 : Nat)).run (9 : Nat) = Part.some (finalExit, 12) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, finalLoop, stepLoop, ExplicitRuntime.bodyAction,
    callCase_run, call_run, instruction, StateT.run_bind, StateT.run_pure, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some, Elgot.StateT.distribute, Function.comp_def, finalExit]

private theorem firstDone : observe (ε := Bool) stage.graph (1 : Nat) (0 : Nat) =
    Part.some (ExplicitRuntime.exitTuple (exit 6, (6 : Nat))) := by
  rw [stage, loop_observe, ExplicitRuntime.graph_observe, firstRun, Part.map_some]

private theorem prefixDone : observe (ε := Bool) firstTwo.graph (1 : Nat) (0 : Nat) =
    Part.some (ExplicitRuntime.exitTuple (exit 13, (9 : Nat))) := by
  change observe (ε := Bool) (joinedGraph stage.code stage.code) (1 : Nat) (0 : Nat) = _
  rw [splice_after _ _ _ _ _ _ firstDone]
  change observe (ε := Bool) (Spine.loop stepLoop).graph (6 : Nat) (6 : Nat) = _
  rw [loop_observe, ExplicitRuntime.graph_observe, secondRun, Part.map_some]

private theorem pipelineDone : observe (ε := Bool) pipeline.graph (1 : Nat) (0 : Nat) =
    Part.some (ExplicitRuntime.exitTuple (finalExit, (12 : Nat))) := by
  change observe (ε := Bool) (joinedGraph firstTwo.code finalStage.code) (1 : Nat) (0 : Nat) = _
  rw [splice_after _ _ _ _ _ _ prefixDone]
  change observe (ε := Bool) (Spine.loop finalLoop).graph (13 : Nat) (9 : Nat) = _
  rw [loop_observe, ExplicitRuntime.graph_observe, finalRun, Part.map_some]

-- The first θ feeds back once. Later bodies see the tokens accumulated at
-- the two cuts, and the flat recovered CFG returns the same typed exit.
example (coherent : RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)) :
    Recognize.recognize pipeline.graph = some recovered ∧
      (Region.denote (ε := Bool) (m := Runtime) recovered.recover.typing (PUnit.unit, (1 : Nat))).run 0 =
        Part.some (finalExit, 12) := by
  refine ⟨pipelineRecognized, ?_⟩
  apply (recovered.region_returns_iff coherent _ _ _ _).mp
  exact (NestedTheta.Partial.observe_eq_some _ _ _ _).mp pipelineDone

private def selectingLoop : Loop Op number number number unitTy number :=
  { finalLoop with header := ⟨.selectExit, rfl, rfl⟩ }

private def conditionalTail : Loop Op number number number unitTy number :=
  { finalLoop with body := .instruction ⟨.maybeBody, rfl, rfl⟩ }

private def routed : Flat.Fragment Op number unitTy number :=
  Flat.linkBy (.loop selectingLoop) (.loop conditionalTail) ⟨.first, .consumer⟩

private abbrev Coherent := RegionCoherent (τ := Ty) (Φ := Op) (ε := Bool) (m := Runtime)
private abbrev RoutedExit := LabelDen [unitTy,number]

private theorem bypassStep :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) selectingLoop) (0 : Nat)).run 0 =
      Part.some ((.inl PUnit.unit : RoutedExit), 1) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, selectingLoop, callCase_run,
    instruction, Elgot.StateT.distribute]

private theorem producerReturns (input : Nat) (nonzero : input ≠ 0) :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) selectingLoop) input).run 0 =
      Part.some ((.inr (.inl (input + 5)) : RoutedExit), 6) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  refine .more (a' := ((input + 1 : Nat), 3)) ?_ (.done ?_)
  all_goals
    simp [Elgot.StateT.body, ExplicitRuntime.round, selectingLoop, finalLoop, stepLoop,
      ExplicitRuntime.bodyAction, callCase_run, call_run, instruction, Elgot.StateT.distribute,
      StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some,
      Function.comp_def, nonzero, Nat.add_assoc]

private theorem consumerReturns :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) conditionalTail) (6 : Nat)).run 6 =
      Part.some ((.inr (.inl (13 : Nat)) : RoutedExit), 9) := by
  rw [Elgot.StateT.run_iter, Part.eq_some_iff, Elgot.Part.mem_iter_iff]
  apply Elgot.Part.Runs.done
  simp [Elgot.StateT.body, ExplicitRuntime.round, conditionalTail, finalLoop, stepLoop,
    ExplicitRuntime.bodyAction, callCase_run, call_run, instruction, Elgot.StateT.distribute,
    StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some,
    Function.comp_def]

private theorem consumerUndefined :
    (iter (ExplicitRuntime.round (ε := Bool) (m := Runtime) conditionalTail) (9 : Nat)).run 6 =
      Part.none := by
  rw [Elgot.StateT.run_iter, Part.eq_none_iff]
  intro result finite
  rw [Elgot.Part.mem_iter_iff] at finite
  have blocked : Elgot.StateT.body (ExplicitRuntime.round (ε := Bool) (m := Runtime) conditionalTail)
      ((9 : Nat),6) = Part.none := by
    simp [Elgot.StateT.body, ExplicitRuntime.round, conditionalTail, finalLoop,
      ExplicitRuntime.bodyAction, callCase_run, call_run, instruction,
      StateT.run_bind, Part.bind_eq_bind]
  cases finite with
  | done h | more h _ => rw [blocked] at h; exact Part.notMem_none _ h

private theorem routed_run (coherent : Coherent) (input : Nat) :
    Region.denote (ε := Bool) (m := Runtime) routed.typing (PUnit.unit,input) =
      iter (ExplicitRuntime.round (ε := Bool) selectingLoop) input >>= fun
        | .inl result => pure (.inl result)
        | .inr (.inl payload) => iter (ExplicitRuntime.round (ε := Bool) conditionalTail) payload
        | .inr (.inr impossible) => nomatch impossible := by
  rw [routed, Flat.denote_linkBy _ _ _ coherent]
  simp only [Flat.Fragment.loop_denote, ExplicitRuntime.denote_rounds _ coherent]
  congr 1
  funext exit
  rcases exit with result | payload | impossible
  · rfl
  · rfl
  · exact impossible.elim

-- The first label skips the consumer's effects. The heterogeneous second
-- label goes through feedback and carries the producer token to the consumer.
example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.typing (PUnit.unit,(0 : Nat))).run 0 =
      Part.some ((.inl PUnit.unit : RoutedExit), 1) := by
  rw [routed_run coherent, StateT.run_bind, bypassStep]
  simp only [Part.bind_eq_bind, Part.bind_some, StateT.run_pure, Part.pure_eq_some]

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.typing (PUnit.unit,(1 : Nat))).run 0 =
      Part.some ((.inr (.inl (13 : Nat)) : RoutedExit), 9) := by
  rw [routed_run coherent, StateT.run_bind, producerReturns 1 (by decide)]
  exact (Part.bind_some _ _).trans consumerReturns

example (coherent : Coherent) :
    (Region.denote (ε := Bool) (m := Runtime) routed.typing (PUnit.unit,(4 : Nat))).run 0 =
      Part.none := by
  rw [routed_run coherent, StateT.run_bind, producerReturns 4 (by decide)]
  exact (Part.bind_some _ _).trans consumerUndefined

private abbrev Start := WirePorts number number number
private abbrev Stop := WirePorts number unitTy number
private abbrev Sigs := [Start, Start, Start, Stop, Stop]
private abbrev Joint := Graph Op number number number number unitTy number Sigs

open OrderedRuntime.Structured (runtime)
open NestedTheta.Equality

private def staleToken {past : List (Ports (OrderedRuntime.Structured.Ty Ty))}
    {t : OrderedRuntime.Structured.Ty Ty} (source : Origin Start past t) : Origin Start past t :=
  if h : runtime = t then Eq.mp (congrArg (Origin Start past) h) (.arg (.tail .head))
  else source

-- The second cut still reads data from θ #2. Its token now refers to the
-- pipeline entry, a well-typed stale reference.
private def stale : Joint :=
  let term : NestedTheta.Term (Wires.Op Op) Start [] Sigs Stop := match pipeline.graph.toTerm with
    | .bind first a (.bind link₁ b (.bind second c (.bind link₂ d tail))) =>
      let inputs := link₂.inputs.map (fun _ wire => staleToken wire)
      .bind first a (.bind link₁ b (.bind second c (.bind { link₂ with inputs } d tail)))
  term.toGraph

private theorem staleDifferent : joinedGraph firstTwo.code finalStage.code ≠ stale := by
  intro equal
  have changed := congrArg (fun g : Joint => (g.nodes (3 : Fin 5)).inputs.addresses) equal
  change [Address.output 2 0, Address.output 2 1] = [Address.output 2 0, Address.arg 1] at changed
  cases changed

example : certifyCut firstTwo.code finalStage.code stale = none := rejectCut staleDifferent

private theorem staleScan : Recognize.scan stale.toTerm = Recognize.scan pipeline.graph.toTerm := by
  unfold stale
  rw [NestedTheta.Term.toTerm_toGraph]
  generalize pipeline.graph.toTerm = term
  cases term with
  | bind first a rest =>
    cases rest with
    | bind link₁ b rest =>
      cases rest with
      | bind second c rest =>
        cases rest with
        | bind link₂ d tail => cases link₂; rfl

-- The labels still parse. Rejection comes from checking the relocated token origin.
private theorem staleParsed : Recognize.candidate stale = some pipeline := by
  have parsed := Recognize.candidate_generated pipeline pipelineForm
  unfold Recognize.candidate at parsed ⊢
  rw [staleScan]
  exact parsed

example : Recognize.recognize stale = none :=
  Recognize.reject_wiring pipeline staleParsed staleDifferent

#eval show IO Unit from do
  unless (Recognize.recognize pipeline.graph).isSome do
    throw (IO.userError "could not recover the three-loop pipeline from its graph")
  unless (Recognize.recognize nestedPipeline.graph).isSome do
    throw (IO.userError "could not recover the nested-choice leaf")
  unless (Recognize.candidate stale).isSome && (Recognize.recognize stale).isNone do
    throw (IO.userError "serial recognition failed to check the stale token")
  unless (certifyCut stage.code stage.code firstTwo.graph).isSome do
    throw (IO.userError "first serial cut was rejected")
  unless (certifyCut firstTwo.code finalStage.code pipeline.graph).isSome do
    throw (IO.userError "second serial cut was rejected")
  unless (certifyCut firstTwo.code finalStage.code stale).isNone do
    throw (IO.userError "second serial cut accepted the stale entry token")

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Tests
