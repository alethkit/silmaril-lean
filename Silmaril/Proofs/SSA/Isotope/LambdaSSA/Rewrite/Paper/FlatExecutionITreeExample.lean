module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Kleisli.Thms

/-! # A visible self-back edge in a typed packed CFG -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open FiniteCFG Semantics.Interaction Elgot.ITree

private inductive Op where
  | start | poll

private abbrev Choice (κ : Type _) : Ty κ := .coprod .unit .unit

local instance {κ : Type _} : HasTy Op (Ty κ) where
  src _ := .unit
  trg _ := Choice κ

private def graph : FiniteCFG Op 1 1 0 :=
  ⟨.br 0 (.op .start .unit), fun _ =>
    .case (.bv 0) (.br 0 (.op .poll (.bv 0))) (.br 1 (.bv 0))⟩

private theorem graph_typed (κ : Type _) : graph.HasType .nil (fun _ => Choice κ) (fun _ => .unit) :=
  ⟨.br (.op .unit), fun _ => .case .bv (.br (.op .bv)) (.br .bv)⟩

private def env : Semantics.Env Empty := fun _ => .unit

private abbrev Run := Tree (Event Op Empty) (Transfer Empty)

private noncomputable def step (p : BlockInput Empty 1) :
    Tree (Event Op Empty) (Transfer Empty ⊕ BlockInput Empty 1) :=
  region request (Semantics.extend env p.2) (graph.block p.1).erase >>= fun out =>
    pure (splitTransfer 1 out)

private noncomputable def next (reply : Value Empty) : Run :=
  iterate step (0, reply) >>= fun p => pure (packedTreeOutput p)

private theorem go_again :
    next (.inl .unit) = vis (.call .poll .unit) next := by
  have unfoldStep := congrFun (iterate_fixpoint step) (0, Value.inl Value.unit)
  change iterate step (0, .inl .unit) =
    (step (0, .inl .unit) >>= Sum.elim pure (iterate step)) at unfoldStep
  rw [next, unfoldStep]
  simp [step, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, request, splitTransfer, -bind_pure_comp]
  rfl

private theorem leave :
    next (.inr .unit) = ret (0, .inl .unit) := by
  have unfoldStep := congrFun (iterate_fixpoint step) (0, Value.inr Value.unit)
  change iterate step (0, .inr .unit) =
    (step (0, .inr .unit) >>= Sum.elim pure (iterate step)) at unfoldStep
  rw [next, unfoldStep]
  simp [step, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, splitTransfer,
    packedTreeOutput, Region.packedExitValue]
  rfl

-- Start is visible first. A left reply reaches the poll on the actual back
-- edge and a second left reply reaches the same poll again. A right reply
-- there leaves through the sole packed outward label.
example :
    out (region request env (packedExecutionRegion (graph_typed Empty))) =
        Part.some (.vis (.call .start .unit) next) ∧
      out (next (.inl .unit)) = Part.some (.vis (.call .poll .unit) next) ∧
      out (next (.inr .unit)) = Part.some (.ret (0, .inl .unit)) := by
  refine ⟨?_, by simp only [go_again, out_vis], by simp only [leave, out_ret]⟩
  rw [packedExecution_tree request]
  change out ((region request env graph.entry.erase >>= fun p =>
    Sum.elim pure (iterate step) (splitTransfer 1 p)) >>= fun p => pure (packedTreeOutput p)) = _
  simp [graph, Flat.erase, Morphism.CaseSSA.erase, region, term, request, splitTransfer, -bind_pure_comp]
  rfl

section TypedReplies

open CategoryTheory
open Semantics.Interaction.Typed
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Region.Paper.TypeCategory (denoteArrow)

private abbrev Atom := PEmpty.{2}

local instance : AtomValues Atom where
  carrier := PEmpty.elim

attribute [local instance] typeModel

local notation "Atoms" => AtomValues.carrier (κ := Atom)

private inductive TypedEvent : Type → Type where
  | call (opcode : Op) (arg : Unit) : TypedEvent Bool

local instance : HasEff Op Bool where
  eff _ := true

local notation "TM" => ModelTree TypedEvent
local notation "J" => typeJ (m := TM)
local notation "T" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)

private def reply (b : Bool) : Ty.denote Atoms (Choice Atom) :=
  if b then .inr PUnit.unit else .inl PUnit.unit

local instance : InstructionModel Op (Ty Atom) Bool TM where
  denote f _ := vis (.call f ()) (fun b => pure (reply b))
  denotePure f h := by cases h
  denote_pure f h := by cases h

attribute [local instance] categoricalInstructions

private def replyValue (b : Bool) : Value (Sigma Atoms) :=
  if b then .inr .unit else .inl .unit

private def raw (f : Op) (_ : Value (Sigma Atoms)) : TM (Value (Sigma Atoms)) :=
  vis (.call f ()) (fun b => pure (replyValue b))

private theorem compatible :
    Compatible (κ' := Atom) ⟨fun f x =>
      InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TM) f x⟩ raw := by
  intro f x
  change raw f .unit =
    (vis (.call f ()) (fun b => (pure (reply b) : TM _)) >>= fun y =>
      pure (encodeValue Atoms (Choice Atom) y))
  unfold raw
  rw [vis_bind]
  congr 1
  funext b
  cases b <;> simp only [pure_bind] <;> rfl

private def typedEnv : Semantics.Env (Sigma Atoms) := fun _ => .unit

private abbrev RunTyped := TM (Transfer (Sigma Atoms))

private noncomputable def typedStep (p : BlockInput (Sigma Atoms) 1) :
    TM (Transfer (Sigma Atoms) ⊕ BlockInput (Sigma Atoms) 1) :=
  region raw (Semantics.extend typedEnv p.2) (graph.block p.1).erase >>= fun out =>
    pure (splitTransfer 1 out)

private noncomputable def typedNext (b : Bool) : RunTyped :=
  iterate typedStep (0, replyValue b) >>= fun p => pure (packedTreeOutput p)

private noncomputable def observedArrow : RunTyped :=
  (show TM _ from (denoteArrow J T (packedExecution (graph_typed Atom))).of PUnit.unit) >>=
    fun b => pure (0, encodeValue Atoms _ b)

private abbrev StateShape : Ty Atom := Region.packedExitType [Choice Atom]
private abbrev ExitShape : Ty Atom := Region.packedExitType [.unit]

private noncomputable def observedDispatcher : RunTyped :=
  (show TM _ from (Region.Paper.TypeCategory.denoteSumArrow J T
    (packedDispatcher (graph_typed Atom))).of
      (show Ty.denote Atoms StateShape from .inl (.inl PUnit.unit))) >>= fun t =>
    pure (0, encodeValue Atoms (.coprod ExitShape StateShape)
      ((CategoryTheory.Limits.Types.binaryCoproductIso (Ty.denote Atoms ExitShape)
        (Ty.denote Atoms StateShape)).hom t))

-- A selected block visibly polls before returning the packed recurrence tag.
example :
    out observedDispatcher =
      Part.some (.vis (.call .poll ()) (fun b => ret (0, .inr (.inl (replyValue b))))) := by
  have evaluated := packedDispatcher_kleisli_sum_tree raw compatible (graph_typed Atom)
    (show Ty.denote Atoms StateShape from .inl (.inl PUnit.unit)) typedEnv
  change observedDispatcher = _ at evaluated
  rw [evaluated]
  change out (region raw (Semantics.extend typedEnv (Region.packedExitValue (0 : Fin 1).val (.inl .unit)))
    (packedDispatcherRegion (graph_typed Atom))) = _
  rw [packedBlock_tree raw (graph_typed Atom) (0 : Fin 1) typedEnv (.inl .unit)]
  simp [graph, Flat.erase, Morphism.CaseSSA.erase, region, term, raw,
    routeValue, Region.packedExitValue, -bind_pure_comp]
  rfl

-- The same graph now runs from its categorical arrow with typed replies.
example :
    out observedArrow = Part.some (.vis (.call .start ()) typedNext) ∧
      out (typedNext false) = Part.some (.vis (.call .poll ()) typedNext) ∧
      out (typedNext true) = Part.some (.ret (0, .inl .unit)) := by
  have stepUnfold (b : Bool) : iterate typedStep (0, replyValue b) =
      (typedStep (0, replyValue b) >>= Sum.elim pure (iterate typedStep)) :=
    congrFun (iterate_fixpoint typedStep) (0, replyValue b)
  refine ⟨?_, ?_, ?_⟩
  · rw [observedArrow, packedExecution_kleisli_tree raw compatible]
    change out ((region raw typedEnv graph.entry.erase >>= fun p =>
      Sum.elim pure (iterate typedStep) (splitTransfer 1 p)) >>= fun p => pure (packedTreeOutput p)) = _
    simp [graph, Flat.erase, Morphism.CaseSSA.erase, region, term, raw, splitTransfer, -bind_pure_comp]
    rfl
  · rw [typedNext, stepUnfold]
    simp [typedStep, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, raw, replyValue,
      splitTransfer, -bind_pure_comp]
    rfl
  · rw [typedNext, stepUnfold]
    simp [typedStep, graph, Flat.erase, Morphism.CaseSSA.erase, region, term, replyValue,
      splitTransfer, packedTreeOutput, Region.packedExitValue]
    exact out_ret _

end TypedReplies

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeExample
