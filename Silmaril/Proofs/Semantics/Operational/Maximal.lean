module

public import Silmaril.Semantics.Operational.Maximal.Defs

public section

namespace Silmaril.Proofs.Semantics.Operational.Maximal

open Silmaril.Semantics.Operational

variable {P S T L K O V Ω : Type*}

theorem visiblePrefixes_of_silent (labels : Cslib.ωSequence (Option L)) (silent : ∀ n, labels n = none) :
    visiblePrefixes labels = {[]} := by
  have erases (n : Nat) : (Cslib.ωSequence.take n labels).filterMap id = [] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Cslib.ωSequence.take_succ' n, List.filterMap_append, ih, silent n]
      rfl
  ext log
  change (∃ n, (Cslib.ωSequence.take n labels).filterMap id = log) ↔ log = []
  constructor
  · rintro ⟨n, eq⟩
    exact eq.symm.trans (erases n)
  · rintro rfl
    exact ⟨0, rfl⟩

theorem path_iff_reach (sem : Labelled S L O) (start last : S) :
    (∃ log, sem.Path start log last) ↔ sem.toOpSem.Reach start last := by
  constructor
  · rintro ⟨log, path⟩
    induction path with
    | nil => exact .refl
    | silent first _ tail => exact tail.head ⟨none, first⟩
    | visible first _ tail => exact tail.head ⟨some _, first⟩
  · intro path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], .nil last⟩
    | head first _ ih =>
      obtain ⟨label, first⟩ := first
      obtain ⟨log, tail⟩ := ih
      cases label with
      | none => exact ⟨log, .silent first tail⟩
      | some event => exact ⟨event :: log, .visible first tail⟩

theorem diverges_iff (sem : RunSem S L O) (start : S) :
    sem.toWithUB.toOpSem.Diverges start ↔ ∃ prefixes, sem.Observes start (.diverges prefixes) := by
  constructor
  · rintro ⟨states, first, steps⟩
    classical
    let labels : Cslib.ωSequence (Option L) := ⟨fun n => Classical.choose (steps n)⟩
    exact ⟨visiblePrefixes labels, ⟨states⟩, labels, first,
      fun n => Classical.choose_spec (steps n), rfl⟩
  · rintro ⟨_, states, labels, first, steps, _⟩
    exact ⟨states.get, first, fun n => ⟨labels n, steps n⟩⟩

theorem exists_observation (sem : RunSem S L O) (start : S) : ∃ obs, sem.Observes start obs := by
  classical
  let raw := sem.toWithUB.toOpSem
  by_cases finite : ∃ last, raw.Reach start last ∧ raw.Normal last
  · obtain ⟨last, reach, normal⟩ := finite
    obtain ⟨log, path⟩ := (path_iff_reach sem.toLabelled start last).mpr reach
    by_cases terminal : ∃ outcome, sem.observe last outcome
    · obtain ⟨outcome, seen⟩ := terminal
      exact ⟨.finite log (.terminal outcome), last, path, normal, seen⟩
    · have noOutcome (outcome : Outcome O) : ¬ sem.observe last outcome :=
        fun seen => terminal ⟨outcome, seen⟩
      by_cases waiting : sem.blocked last
      · exact ⟨.finite log .blocked, last, path, normal, noOutcome, waiting⟩
      · exact ⟨.finite log .stuck, last, path, normal, noOutcome, waiting⟩
  · have diverges : raw.Diverges start := by
      apply InfiniteTrace.coinduct (raw.Reach start) ?_ .refl
      intro state reachable
      by_contra noSuccessor
      apply finite
      exact ⟨state, reachable, fun target edge => noSuccessor ⟨target, edge, reachable.tail edge⟩⟩
    obtain ⟨prefixes, observed⟩ := (diverges_iff sem start).mp diverges
    exact ⟨.diverges prefixes, observed⟩

theorem raw_nonempty_iff (model : HasRuns P S L O) (view : RunObservation L O → Ω) (program : P) :
    (model.raw view program).Nonempty ↔ ∃ start, model.initial program start := by
  constructor
  · rintro ⟨_, _, ⟨start, entry, _⟩, _⟩
    exact ⟨start, entry⟩
  · rintro ⟨start, entry⟩
    obtain ⟨obs, observed⟩ := exists_observation model.semantics start
    exact ⟨view obs, obs, ⟨start, entry, observed⟩, rfl⟩

theorem terminates_iff (model : HasRuns P S L O) (program : P) :
    model.Terminates program ↔ ∀ prefixes, ¬ model.Observes program (.diverges prefixes) := by
  constructor
  · rintro terminates prefixes ⟨start, entry, observed⟩
    exact terminates entry ((diverges_iff model.semantics start).mpr ⟨prefixes, observed⟩)
  · intro noDivergentRun start entry infinite
    obtain ⟨prefixes, observed⟩ := (diverges_iff model.semantics start).mp infinite
    exact noDivergentRun prefixes ⟨start, entry, observed⟩

theorem raw_le_completed
    {concrete : HasRuns P S L O} {abstract : HasRuns P T K V}
    {concreteView : RunObservation L O → Ω} {abstractView : RunObservation K V → Ω}
    {program : P} {rel : S → T → Prop}
    (coverage : RunCoverage concrete abstract concreteView abstractView program rel) :
    concrete.raw concreteView program ⊆ abstract.completed abstractView program := by
  rintro observation ⟨run, ⟨start, entry, execution⟩, rfl⟩
  obtain ⟨target, targetEntry, related⟩ := coverage.entry entry
  rcases coverage.run related execution with reachable | ⟨other, execution, same⟩
  · exact Or.inl ⟨target, targetEntry, reachable⟩
  · exact Or.inr ⟨other, ⟨target, targetEntry, execution⟩, same.symm⟩

end Silmaril.Proofs.Semantics.Operational.Maximal
