module

public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Data.Set.Lattice.Indexed
public import Silmaril.Semantics.Operational.Determinism.Defs
public import Silmaril.Semantics.Operational.Program.Defs

/-!
# Maximal operational observations

Finite runs end at a state with no outgoing transition. An explicit outcome
takes precedence over waiting, and a remaining dead end is stuck. Infinite
runs are observations in their own right, with or without visible events.
-/

@[expose] public section

namespace Silmaril.Semantics.Operational

variable {P S T L K O V Ω : Type*}

def Labelled.toLTS (sem : Labelled S L O) : Cslib.LTS S (Option L) :=
  ⟨sem.step⟩

def Labelled.toOpSem (sem : Labelled S L O) : OpSem S O where
  step s t := ∃ label, sem.step s label t
  observe := sem.observe

/-- The visible prefixes of an infinite sequence of steps. A sequence with
finitely many visible events has a longest visible prefix. -/
def visiblePrefixes (labels : Cslib.ωSequence (Option L)) : Set (List L) :=
  { log | ∃ n, (Cslib.ωSequence.take n labels).filterMap id = log }

inductive RunEnd (O : Type*) where
  | terminal (outcome : Outcome O)
  | blocked
  | stuck

inductive RunObservation (L O : Type*) where
  | finite (log : List L) (ending : RunEnd O)
  | diverges (prefixes : Set (List L))

structure RunSem (S L O : Type*) extends Labelled S L O where
  /-- The environment can be waited on at this state. The endpoint policy
  consults this predicate only at a dead end with no terminal outcome. -/
  blocked : S → Prop
  ub : S → Prop

namespace RunSem

def toWithUB (sem : RunSem S L O) : WithUB S O :=
  ⟨sem.toLabelled.toOpSem, sem.ub⟩

/-- A finite run is maximal at quiescence. An observation at a state with
successors can still count for ordinary `May`, whose contract is weaker. -/
def EndAt (sem : RunSem S L O) (state : S) (ending : RunEnd O) : Prop :=
  sem.toWithUB.toOpSem.Normal state ∧
    match ending with
    | .terminal outcome => sem.observe state outcome
    | .blocked => (∀ outcome, ¬ sem.observe state outcome) ∧ sem.blocked state
    | .stuck => (∀ outcome, ¬ sem.observe state outcome) ∧ ¬ sem.blocked state

/-- Raw observations ignore the UB predicate. Infinite observations use an
actual CSLib execution, with silent steps erased only in the observation. -/
def Observes (sem : RunSem S L O) (start : S) : RunObservation L O → Prop
  | .finite log ending => ∃ last, sem.toLabelled.Path start log last ∧ sem.EndAt last ending
  | .diverges prefixes => ∃ states labels, states 0 = start ∧
      sem.toLabelled.toLTS.OmegaExecution states labels ∧ visiblePrefixes labels = prefixes

end RunSem

/-- Relational entry allows several starts or no admitted start. -/
structure HasRuns (P S L O : Type*) where
  initial : P → S → Prop
  semantics : RunSem S L O

/-- The pointwise complete lattice of sets over a common program and
observation interface. Lower elements admit fewer observations. -/
abbrev RunBehaviors (P Ω : Type*) := P → Set Ω

namespace HasRuns

def toHasOpSem (model : HasRuns P S L O) : HasOpSem P S O :=
  ⟨model.initial, model.semantics.toWithUB⟩

def Observes (model : HasRuns P S L O) (program : P) (obs : RunObservation L O) : Prop :=
  ∃ start, model.initial program start ∧ model.semantics.Observes start obs

def raw (model : HasRuns P S L O) (view : RunObservation L O → Ω) : RunBehaviors P Ω :=
  fun program => { o | ∃ obs, model.Observes program obs ∧ view obs = o }

/-- Per-program coarse UB completion. If any entry reaches a marked state
via the raw steps, the program admits every observation in the common
carrier. Reachability includes the empty path. The marker takes precedence
even if its state also has a terminal outcome or a blocked/stuck reading.
With no entry, the set is empty. This policy discards all prefix constraints. -/
def completed (model : HasRuns P S L O) (view : RunObservation L O → Ω) : RunBehaviors P Ω :=
  fun program => { o | model.toHasOpSem.UBReachable program ∨ o ∈ model.raw view program }

/-- Every admitted start has only finite maximal runs. This also permits
blocked and stuck endings. Entry existence is a separate condition. -/
def Terminates (model : HasRuns P S L O) (program : P) : Prop :=
  ∀ ⦃start⦄, model.initial program start → ¬ model.semantics.toWithUB.toOpSem.Diverges start

end HasRuns

/-- Coverage uses a matched abstract entry for each concrete entry. At
related starts, each concrete maximal observation either has a matching
abstract run in the common view or the abstract start reaches a UB marker.
The latter case uses the coarse completion policy. -/
structure RunCoverage (concrete : HasRuns P S L O) (abstract : HasRuns P T K V)
    (concreteView : RunObservation L O → Ω) (abstractView : RunObservation K V → Ω)
    (program : P) (rel : S → T → Prop) : Prop where
  entry : ∀ ⦃start⦄, concrete.initial program start →
    ∃ target, abstract.initial program target ∧ rel start target
  run : ∀ ⦃start target obs⦄, rel start target → concrete.semantics.Observes start obs →
    abstract.semantics.toWithUB.UBReachable target ∨
      ∃ other, abstract.semantics.Observes target other ∧ concreteView obs = abstractView other

end Silmaril.Semantics.Operational
