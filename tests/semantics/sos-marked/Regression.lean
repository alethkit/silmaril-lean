module

import Silmaril.Logic.Operational.SOS.Marked.Policy.Thms
import Silmaril.Logic.Operational.Thms
meta import Silmaril.Logic.Operational.SOS.Marked.Thms

open CategoryTheory Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS
open Silmaril.Logic.Operational.SOS.Marked Silmaril.Semantics.SOS
open Silmaril.Logic.Institution (Inst)
open Silmaril.Semantics.Operational (Outcome)

private abbrev carriers : Carriers := ⟨⟨Nat, Bool⟩, Bool, Nat⟩

private def shift : carriers ⟶ carriers :=
  ⟨⟨Nat.succ, Bool.not⟩, Bool.not, Nat.succ⟩

private def entry (p : Bool) (n : Nat) : MarkedJudgment carriers := .inl (.entry p n)
private def edge (n : Nat) (b : Bool) : MarkedJudgment carriers := .inl (.step (n, b, n + 1))

private def entryFact (p : Bool) (n : Nat) : Rule (MarkedJudgment carriers) :=
  ⟨[], entry p n⟩

private def ubFact (n : Nat) : Rule (MarkedJudgment carriers) :=
  ⟨[], ubJudgment n⟩

private def stepRule (p : Bool) (n : Nat) (b : Bool) : Rule (MarkedJudgment carriers) :=
  ⟨[entry p n, ubJudgment n], edge n b⟩

private def endpointRule (n : Nat) (b : Bool) : Rule (MarkedJudgment carriers) :=
  ⟨[edge n b], .inl (.endpoint (n + 1) (.returned n))⟩

private def rules : MarkedRules :=
  ⟨carriers, {r | (∃ p n, r = entryFact p n) ∨ (∃ n, r = ubFact n) ∨
    (∃ p n b, r = stepRule p n b) ∨ (∃ n b, r = endpointRule n b)}⟩

private def ruleShift : rules ⟶ rules where
  sig := shift
  mapsTo := by
    rintro _ (⟨p, n, rfl⟩ | ⟨n, rfl⟩ | ⟨p, n, b, rfl⟩ | ⟨n, b, rfl⟩)
    · exact Or.inl ⟨!p, n.succ, rfl⟩
    · exact Or.inr (Or.inl ⟨n.succ, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨!p, n.succ, !b, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨n.succ, !b, rfl⟩))

private abbrev marked : WithMarker := (RulePresentation.interpret markedShapes).obj rules
private abbrev ordinary : Ordinary := forget.obj marked

private theorem entryProved (p : Bool) (n : Nat) : marked.model (entry p n) :=
  Derives.apply (r := entryFact p n) (Or.inl ⟨p, n, rfl⟩) (fun _ h => nomatch h)

private theorem ubProved (n : Nat) : marked.model (ubJudgment n) :=
  Derives.apply (r := ubFact n) (Or.inr (Or.inl ⟨n, rfl⟩)) (fun _ h => nomatch h)

private theorem edgeProved (n : Nat) (b : Bool) : marked.model (edge n b) :=
  Derives.apply (r := stepRule false n b) (Or.inr (Or.inr (Or.inl ⟨false, n, b, rfl⟩)))
    fun _ h => by
      simp only [stepRule, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · exact entryProved false n
      · exact ubProved n

private theorem endpointProved (n : Nat) (b : Bool) :
    marked.model (.inl (.endpoint (n + 1) (.returned n))) :=
  Derives.apply (r := endpointRule n b) (Or.inr (Or.inr (Or.inr ⟨n, b, rfl⟩)))
    fun _ h => by
      have hj := List.mem_singleton.mp h
      subst hj
      exact edgeProved n b

private theorem twoSteps :
    Runs marked.system.model (0 : Nat) [true, false] (2 : Nat) :=
  .stepL (edgeProved 0 true) (.stepL (edgeProved 1 false) .refl)

example : Runs ordinary.system.model (0 : Nat) [true, false] (2 : Nat) := twoSteps

example : Runs ordinary.system.model (1 : Nat) [false, true] (3 : Nat) :=
  System.Hom.runs
    ((Interpretation.toSystems ordinaryShapes).map
      (forget.map ((RulePresentation.interpret markedShapes).map ruleShift))) twoSteps

example : marked.toHasOpSem.initial true (0 : Nat) := entryProved true 0
example : ordinary.toOpSem.observe (1 : Nat) (.returned (0 : Nat)) := endpointProved 0 true

-- Erasing rules mentioning UB leaves just the entry facts in this presentation.
private def erasedRules : OrdinaryRules :=
  ⟨carriers, {r | ∃ p n, r = ⟨[], .entry p n⟩}⟩

private theorem erasedClosed :
    Closed erasedRules.axioms (fun j : Judgment carriers => match j with
      | .entry _ _ => True
      | _ => False) := by
  rintro _ ⟨p, n, rfl⟩ _
  trivial

example : ordinary.system.model ((0 : Nat), true, (1 : Nat)) ∧
    ¬ ((RulePresentation.interpret ordinaryShapes).obj erasedRules).system.model ((0 : Nat), true, (1 : Nat)) :=
  ⟨edgeProved 0 true, fun h => Derives.least h erasedClosed⟩

private def ordinaryClause : Sentence (Judgment carriers) :=
  .clause ⟨[.entry false 0, .step (0, true, 1)], .endpoint 1 (.returned 0)⟩

example :
    (markedInstitution.obj carriers).Sat (Discrete.mk marked.model)
        ((includeSentences.app carriers).sen ordinaryClause) ↔
      (ordinaryInstitution.obj carriers).Sat (Discrete.mk ordinary.model) ordinaryClause :=
  Inst.CoHom.satisfaction toMarked carriers (Discrete.mk marked.model) ordinaryClause

example :
    (markedInstitution.obj carriers).Sat (Discrete.mk marked.model)
        ((includeSentences.app carriers).sen ordinaryClause) ↔
      (ordinaryInstitution.obj carriers).Sat (Discrete.mk ordinary.model) ordinaryClause :=
  Inst.Hom.satisfaction toOrdinary carriers (Discrete.mk marked.model) ordinaryClause

example :
    ordinaryClause.Sat ordinary.model ∧
      (.atom (ubJudgment 0) : Sentence (MarkedJudgment carriers)).Sat marked.model ∧
      ¬ (.atom (ubJudgment 0) : Sentence (MarkedJudgment carriers)).Sat
        (emptyMarker.obj ordinary).model :=
  ⟨fun _ => endpointProved 0 true, ubProved 0, id⟩

private def enterMarked : emptyMarker.obj ordinary ⟶ marked :=
  (emptyMarkerAdjunction.homEquiv ordinary marked).symm (𝟙 ordinary)

example : enterMarked.carriers = 𝟙 carriers := rfl

-- The ordinary identity exists after forgetting, while the marked map in the
-- other direction cannot preserve a true UB judgment.
example (f : marked ⟶ emptyMarker.obj ordinary) : False :=
  f.preserves (ubJudgment (0 : Nat)) (ubProved 0)

example : (emptyMarker.obj ordinary).toHasOpSem.semantics.SafeAt (0 : Nat) :=
  emptyMarker_safe ordinary (0 : Nat)

example :
    marked.toHasOpSem.semantics.SafeAt (shift.signature.state 0) →
      marked.toHasOpSem.semantics.SafeAt (0 : Nat) :=
  Interpretation.Hom.safe_of_safe ((RulePresentation.interpret markedShapes).map ruleShift)

private abbrev escapeCarriers : Carriers := ⟨⟨Bool, Unit⟩, Unit, Unit⟩
private def noEdges : Ordinary := ⟨escapeCarriers, fun _ => False⟩
private def escape : WithMarker := ⟨escapeCarriers, fun
  | .inl (.step (false, (), true)) => True
  | .inr true => True
  | _ => False⟩

private def toEscape : emptyMarker.obj noEdges ⟶ escape :=
  ⟨⟨⟨fun _ => false, id⟩, id, id⟩, fun j h => by cases j <;> exact False.elim h⟩

example : Interpretation.Hom.ReflectsUB toEscape := fun _ h => h
example : ¬ Interpretation.Hom.LiftsSteps toEscape :=
  fun lift => let ⟨_, _, edge, _, _⟩ := lift false () true trivial; edge

example : (emptyMarker.obj noEdges).toHasOpSem.semantics.SafeAt false ∧
    ¬ escape.toHasOpSem.semantics.SafeAt (toEscape.carriers.signature.state false) :=
  ⟨emptyMarker_safe noEdges false, fun safe => safe ⟨true, .single ⟨(), trivial⟩, trivial⟩⟩

example (s : Bool) :
    escape.toHasOpSem.semantics.SafeAt s ↔ escape.toHasOpSem.semantics.SafeAt s :=
  Interpretation.Hom.safe_iff (𝟙 escape) (fun _ l t h => ⟨l, t, h, rfl, rfl⟩) (fun _ h => h) s

-- Execute the actual ground rule translation, including its marker and payload.
private def showJudgment : MarkedJudgment carriers → String
  | .inl (.entry p s) => s!"entry {p} {s}"
  | .inl (.step (s, l, t)) => s!"step {s} {l} {t}"
  | .inl (.endpoint s (.returned n)) => s!"return {s} {n}"
  | .inl (.endpoint s .trap) => s!"trap {s}"
  | .inr s => s!"ub {s}"

public def main : IO Unit := do
  let mapRule := Rule.map (markedShapes.map shift).judgment
  let step := mapRule (stepRule false 0 true)
  let finish := mapRule (endpointRule 0 true)
  unless step.premises.map showJudgment == ["entry true 1", "ub 1"] &&
      showJudgment step.conclusion == "step 1 false 2" &&
      finish.premises.map showJudgment == ["step 1 false 2"] &&
      showJudgment finish.conclusion == "return 2 1" &&
      showJudgment ((markedShapes.map shift).judgment (.inl (.endpoint 0 .trap))) == "trap 1" do
    throw (IO.userError "unexpected marked SOS translation")
  IO.println "marked SOS translation passed"
