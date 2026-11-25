module

public import Silmaril.Semantics.Operational.Maximal.Defs
import Silmaril.Proofs.Semantics.Operational.Maximal

@[expose] public section

namespace Silmaril.Semantics.Operational

variable {P S T L K O V Ω : Type*}

theorem visiblePrefixes_of_silent (labels : Cslib.ωSequence (Option L)) (silent : ∀ n, labels n = none) :
    visiblePrefixes labels = {[]} :=
  Proofs.Semantics.Operational.Maximal.visiblePrefixes_of_silent labels silent

theorem Labelled.path_iff_reach (sem : Labelled S L O) (start last : S) :
    (∃ log, sem.Path start log last) ↔ sem.toOpSem.Reach start last :=
  Proofs.Semantics.Operational.Maximal.path_iff_reach sem start last

/-- Erasing labels from infinite executions recovers the policy API's
divergence, including executions that emit no visible events. -/
theorem RunSem.diverges_iff (sem : RunSem S L O) (start : S) :
    sem.toWithUB.toOpSem.Diverges start ↔ ∃ prefixes, sem.Observes start (.diverges prefixes) :=
  Proofs.Semantics.Operational.Maximal.diverges_iff sem start

theorem RunSem.exists_observation (sem : RunSem S L O) (start : S) : ∃ obs, sem.Observes start obs :=
  Proofs.Semantics.Operational.Maximal.exists_observation sem start

namespace RunBehaviors

theorem mem_sInf {family : Set (RunBehaviors P Ω)} {program : P} {observation : Ω} :
    observation ∈ (sInf family) program ↔ ∀ B ∈ family, observation ∈ B program := by
  simp [sInf_apply, Set.iInf_eq_iInter, Set.mem_iInter]

theorem mem_sSup {family : Set (RunBehaviors P Ω)} {program : P} {observation : Ω} :
    observation ∈ (sSup family) program ↔ ∃ B ∈ family, observation ∈ B program := by
  simp [sSup_apply, Set.iSup_eq_iUnion, Set.mem_iUnion]

end RunBehaviors

namespace HasRuns

variable (model : HasRuns P S L O) (view : RunObservation L O → Ω) (program : P)

theorem raw_le_completed : model.raw view ≤ model.completed view :=
  fun _ _ observed => Or.inr observed

theorem completed_of_safe (safe : ¬ model.toHasOpSem.UBReachable program) :
    model.completed view program = model.raw view program :=
  Set.ext fun _ => or_iff_right safe

theorem completed_of_ub (reachable : model.toHasOpSem.UBReachable program) :
    model.completed view program = Set.univ :=
  Set.ext fun obs => iff_of_true (Or.inl reachable) (Set.mem_univ obs)

/-- Non-vacuity is characterized by entry existence, independently of
termination. A dead end always has an ending and a live infinite run is
itself observable. -/
theorem raw_nonempty_iff :
    (model.raw view program).Nonempty ↔ ∃ start, model.initial program start :=
  Proofs.Semantics.Operational.Maximal.raw_nonempty_iff model view program

theorem terminates_iff :
    model.Terminates program ↔ ∀ prefixes, ¬ model.Observes program (.diverges prefixes) :=
  Proofs.Semantics.Operational.Maximal.terminates_iff model program

end HasRuns

namespace RunCoverage

variable {concrete : HasRuns P S L O} {abstract : HasRuns P T K V}
  {concreteView : RunObservation L O → Ω} {abstractView : RunObservation K V → Ω}
  {program : P} {rel : S → T → Prop}

theorem raw_le_completed
    (coverage : RunCoverage concrete abstract concreteView abstractView program rel) :
    concrete.raw concreteView program ⊆ abstract.completed abstractView program :=
  Proofs.Semantics.Operational.Maximal.raw_le_completed coverage

/-- Reachable UB in the concrete model must also be possible in the
abstract model to compare both coarse completions. This premise is
`HasOpSem.UBRefines` when the native outcome types agree. -/
theorem completed_le
    (coverage : RunCoverage concrete abstract concreteView abstractView program rel)
    (ub : concrete.toHasOpSem.UBReachable program → abstract.toHasOpSem.UBReachable program) :
    concrete.completed concreteView program ⊆ abstract.completed abstractView program :=
  fun _ seen => seen.elim (fun reachable => Or.inl (ub reachable)) (fun raw => coverage.raw_le_completed raw)

/-- At a safe abstract program, preservation of reachable UB establishes concrete safety.
A universal property in the common view then holds of every concrete run
observation. Entry existence and the choice of observation view remain
independent premises for any non-vacuity or termination claim. -/
theorem safe_transfer
    (coverage : RunCoverage concrete abstract concreteView abstractView program rel)
    (ub : concrete.toHasOpSem.UBReachable program → abstract.toHasOpSem.UBReachable program)
    (safe : ¬ abstract.toHasOpSem.UBReachable program) {Q : Ω → Prop}
    (holds : ∀ obs ∈ abstract.completed abstractView program, Q obs) :
    (¬ concrete.toHasOpSem.UBReachable program) ∧
      ∀ obs, concrete.Observes program obs → Q (concreteView obs) :=
  ⟨fun reachable => safe (ub reachable),
    fun obs seen => holds _ (coverage.raw_le_completed ⟨obs, seen, rfl⟩)⟩

end RunCoverage

end Silmaril.Semantics.Operational
