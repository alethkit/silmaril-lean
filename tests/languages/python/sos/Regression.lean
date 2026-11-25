module

import Silmaril.Languages.Python.Core.Rules.Thms
import Silmaril.Logic.Operational.SOS.Marked.Policy.Thms
import Silmaril.Logic.Operational.Thms

open CategoryTheory
open Silmaril.Languages.Python.Core
open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS
open Silmaril.Semantics.Operational
open Silmaril.Semantics.SOS (Rule)

namespace Silmaril.Tests.PythonRuleCorrespondence

private abbrev pythonSignature : Signature := ⟨State, Option Completion⟩

private abbrev pythonShape : Shape :=
  ⟨pythonSignature, Rules.Judgment, fun (source, label, target) => .edge source label target⟩

private def presentation : Presentation := ⟨pythonShape, Rules.rules⟩

private def native : System Shape.signatures :=
  ⟨pythonShape, fun (source, label, target) => Step source label target⟩

private def toNative : presentation.system ⟶ native :=
  ⟨𝟙 pythonShape, fun h => Rules.step_iff.mp h⟩

private def fromNative : native ⟶ presentation.system :=
  ⟨𝟙 pythonShape, fun h => Rules.step_iff.mpr h⟩

example : toNative ≫ fromNative = 𝟙 presentation.system := System.Hom.ext rfl
example : fromNative ≫ toNative = 𝟙 native := System.Hom.ext rfl

private abbrev decorated : Signature := ⟨State, Bool × Option Completion⟩

private abbrev decoratedShape : Shape :=
  ⟨decorated, Bool × Rules.Judgment, fun (s, (tag, label), t) => (tag, .edge s label t)⟩

private def decorateJudgment (j : Rules.Judgment) : Bool × Rules.Judgment := (true, j)

private def decoratedPresentation : Presentation :=
  ⟨decoratedShape, Rule.map decorateJudgment '' Rules.rules⟩

private def decorate : presentation ⟶ decoratedPresentation :=
  ⟨⟨⟨id, fun label => (true, label)⟩, decorateJudgment, fun _ => rfl⟩, fun r h => ⟨r, h, rfl⟩⟩

private def sum : Body := ⟨.binary .add (.int 2) (.int 5)⟩

-- This run derives the arithmetic transition through two positive premises.
private theorem sumEdge : Rules.Derives (.edge sum.start none (.returning (.int 7))) := by
  have primitive : Rules.Derives (.primitive .add 2 5 (.ok 7)) :=
    .apply (Rules.Schema.add 2 5) (fun _ absent => nomatch absent)
  have expression : Rules.Derives (.expression sum.value (.ok (.int 7))) :=
    .apply (Rules.Schema.compute .add 2 5 (.ok 7)) (fun _ member => (List.mem_singleton.mp member).symm ▸ primitive)
  exact .apply (Rules.Schema.evalValue sum.value (.int 7))
    (fun _ member => (List.mem_singleton.mp member).symm ▸ expression)

private theorem sumRun : Runs presentation.system.model sum.start [none, some (.ok 7)] (.finished (.ok 7)) :=
  .stepL sumEdge (.stepL (.apply (Rules.Schema.ret 7) (fun _ absent => nomatch absent)) .refl)

example : Runs native.model sum.start [none, some (.ok 7)] (.finished (.ok 7)) :=
  System.Hom.runs toNative sumRun

example : Runs decoratedPresentation.system.model sum.start
    [(true, none), (true, some (.ok 7))] (.finished (.ok 7)) :=
  System.Hom.runs (Presentation.toSystems.map decorate) sumRun

example : Discrete.mk presentation.Derives ∈
    (Shape.institution.obj pythonShape).modelsOf presentation.axioms :=
  presentation.derives_models

private def sumClause : Sentence pythonShape.Judgment :=
  .clause ⟨[.primitive .add 2 5 (.ok 7)], .expression sum.value (.ok (.int 7))⟩

-- Satisfaction of the concrete clause is preserved by the strict rule map.
example :
    (sumClause.map decorate.shape.judgment).Sat decoratedPresentation.Derives ∧
    sumClause.Sat (Shape.reduct decorate.shape decoratedPresentation.Derives) := by
  have mapped := decorate.preserves _ (Rules.Schema.compute .add 2 5 (.ok 7))
  have holds := Silmaril.Semantics.SOS.derives_closed _ _ mapped
  exact ⟨holds, (Shape.sat_map decorate.shape _ sumClause).mp holds⟩

example :
    (Shape.signatures ⋙ Signature.institution).map decorate.shape ≫ decoratedShape.edgeCorridor =
      pythonShape.edgeCorridor ≫ Shape.institution.map decorate.shape :=
  Shape.toOperational.η.naturality decorate.shape

example :
    (Shape.institution.obj pythonShape).Sat (Discrete.mk presentation.Derives)
      (.atom (.edge sum.start none (.returning (.int 7)))) :=
  (pythonShape.edgeCorridor.sat (Discrete.mk presentation.Derives) (sum.start, none, .returning (.int 7))).mpr
    sumEdge

private def divZero : Expr := .binary .floorDiv (.int 1) (.int 0)
private def leftError : Body := ⟨.binary .add divZero (.binary .add (.int 2) (.int 5))⟩

private theorem exceptionEdge : Rules.Derives (.edge leftError.start none (.raising .zeroDivisionError)) := by
  have primitive : Rules.Derives (.primitive .floorDiv 1 0 (.error .zeroDivisionError)) :=
    .apply (Rules.Schema.divZero 1) (fun _ absent => nomatch absent)
  have division : Rules.Derives (.expression divZero (.error .zeroDivisionError)) :=
    .apply (Rules.Schema.compute .floorDiv 1 0 (.error .zeroDivisionError))
      (fun _ member => (List.mem_singleton.mp member).symm ▸ primitive)
  have addition : Rules.Derives (.expression leftError.value (.error .zeroDivisionError)) :=
    .apply (Rules.Schema.left .add divZero (.binary .add (.int 2) (.int 5)) (.error .zeroDivisionError))
      (fun _ member => (List.mem_singleton.mp member).symm ▸ division)
  exact .apply (Rules.Schema.evalError leftError.value .zeroDivisionError)
    (fun _ member => (List.mem_singleton.mp member).symm ▸ addition)

example :
    Runs presentation.system.model leftError.start [none, some (.error .zeroDivisionError)]
      (.finished (.error .zeroDivisionError)) :=
  .stepL exceptionEdge (.stepL (.apply (Rules.Schema.raise .zeroDivisionError) (fun _ absent => nomatch absent)) .refl)

example : Rules.Derives (.expression (.binary .floorDiv (.int 7) (.int (-3))) (.ok (.int (-3)))) :=
  Rules.expression_iff.mpr (.compute (.div 7 (-3) (by decide)))

example : ¬ Rules.Derives (.primitive .floorDiv 1 0 (.ok 0)) := by
  intro h
  have eval := BinOp.eval_iff.mpr (Rules.primitive_iff.mp h)
  cases eval

example : ¬ Rules.Derives (.edge leftError.start none (.returning (.binary .add divZero (.int 7)))) :=
  fun h => by
    have eq := (Rules.deterministic h exceptionEdge).2
    cases eq

private abbrev carriers : Marked.Carriers :=
  ⟨pythonSignature, Body, Completion⟩

-- The guard is an interpretation choice. Raw rule derivability remains profile independent.
private def marked (profile : Profile) : Marked.WithMarker :=
  ⟨carriers, fun
    | .inl (.step (s, label, t)) => s.supported profile ∧ Rules.Derives (.edge s label t)
    | .inl (.entry program s) => profile.supports program.value ∧ s = program.start
    | .inl (.endpoint s outcome) => s.supported profile ∧ Observes s outcome
    | .inr s => ¬ s.supported profile⟩

private theorem policyStep (profile : Profile) (s t : State) :
    (marked profile).toHasOpSem.semantics.step s t ↔ (model profile).semantics.step s t := by
  change (∃ label, s.supported profile ∧ Rules.Derives (.edge s label t)) ↔
    s.supported profile ∧ ∃ label, Step s label t
  exact ⟨fun ⟨label, admitted, edge⟩ => ⟨admitted, label, Rules.step_iff.mp edge⟩,
    fun ⟨admitted, label, edge⟩ => ⟨label, admitted, Rules.step_iff.mpr edge⟩⟩

private theorem policyMarker (profile : Profile) (s : State) :
    (marked profile).ub s ↔ (model profile).semantics.ub s :=
  ⟨Or.inr, fun marked => marked.resolve_left id⟩

example (profile : Profile) (body : Body) (s : State) :
    (marked profile).toHasOpSem.initial body s ↔ (model profile).initial body s :=
  Iff.rfl

example (profile : Profile) (s : State) (outcome : Outcome Completion) :
    (marked profile).toHasOpSem.semantics.observe s outcome ↔ (model profile).semantics.observe s outcome :=
  Iff.rfl

example : (marked .arithmetic).toHasOpSem.May leftError (.returned (.error .zeroDivisionError)) := by
  let final := State.finished (.error .zeroDivisionError)
  let middle := State.raising .zeroDivisionError
  have first : (marked .arithmetic).toHasOpSem.semantics.step leftError.start middle :=
    (policyStep .arithmetic _ _).mpr ⟨rfl, none, .expr (.left (.compute (.divZero 1)))⟩
  have last : (marked .arithmetic).toHasOpSem.semantics.step middle final :=
    (policyStep .arithmetic _ _).mpr ⟨rfl, some (.error .zeroDivisionError), .raise .zeroDivisionError⟩
  exact ⟨leftError.start, ⟨rfl, rfl⟩, final, (Relation.ReflTransGen.single first).tail last, rfl, .finished _⟩

example : (marked .addition).toHasOpSem.NoEntry leftError ∧ (marked .addition).ub leftError.start :=
  ⟨noEntry_iff.mpr (by decide), (policyMarker .addition _).mpr (.inr (by decide))⟩

private def markedEdge : Sentence (Marked.Judgment carriers) :=
  .atom (.step (sum.start, none, .returning (.int 7)))

example : (markedEdge.map Marked.includeJudgment).Sat (marked .arithmetic).model :=
  (Marked.satisfaction_include (marked .arithmetic).model markedEdge).mpr ⟨rfl, sumEdge⟩

#print axioms Rules.primitive_iff
#print axioms Rules.expression_iff
#print axioms Rules.step_iff
#print axioms sumRun
#print axioms policyStep

end Silmaril.Tests.PythonRuleCorrespondence
