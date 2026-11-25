module

import Silmaril.Semantics.Operational.Maximal.Thms
import Silmaril.Semantics.Operational.Policy.Thms

open Silmaril.Semantics.Operational

private inductive State where
  | start | finished | waiting | inert | emit | loop
  deriving DecidableEq

private inductive Step : State → Option Bool → State → Prop where
  | finish : Step .start (some true) .finished
  | wait : Step .start (some false) .waiting
  | stall : Step .start none .inert
  | emit : Step .emit (some true) .loop
  | spin : Step .loop none .loop

private def semantics (marked : Bool) : RunSem State Bool Bool where
  step := Step
  observe s o := s = .finished ∧ o = .returned true
  blocked s := s = .waiting ∨ s = .finished
  ub s := marked = true ∧ s = .finished

private def model (marked : Bool) : HasRuns (Option State) State Bool Bool where
  initial p s := p = some s ∨ (p = some .start ∧ s = .loop)
  semantics := semantics marked

private theorem finishEnd : (semantics false).EndAt .finished (.terminal (.returned true)) :=
  ⟨(fun _ ⟨_, step⟩ => nomatch step), rfl, rfl⟩

example : (model false).Observes (some .start) (.finite [true] (.terminal (.returned true))) :=
  ⟨.start, Or.inl rfl, .finished, .visible Step.finish (.nil _), finishEnd⟩

example : ¬ (semantics false).EndAt .finished .blocked :=
  fun ending => ending.2.1 (.returned true) ⟨rfl, rfl⟩

example : (model false).Observes (some .start) (.finite [false] .blocked) :=
  ⟨.start, Or.inl rfl, .waiting, .visible Step.wait (.nil _),
    ⟨(fun _ ⟨_, step⟩ => nomatch step), fun _ obs => State.noConfusion obs.1, Or.inl rfl⟩⟩

example : (model false).Observes (some .start) (.finite [] .stuck) :=
  ⟨.start, Or.inl rfl, .inert, .silent Step.stall (.nil _),
    ⟨(fun _ ⟨_, step⟩ => nomatch step), fun _ obs => State.noConfusion obs.1, by
      rintro (eq | eq) <;> cases eq⟩⟩

private theorem silentLoop : (semantics false).Observes .loop (.diverges {[]}) :=
  ⟨Cslib.ωSequence.const .loop, Cslib.ωSequence.const none, rfl, fun _ => Step.spin,
    visiblePrefixes_of_silent _ (fun _ => rfl)⟩

example : (model false).Observes (some .start) (.diverges {[]}) :=
  ⟨.loop, Or.inr ⟨rfl, rfl⟩, silentLoop⟩

open Cslib.ωSequence in
private theorem emittedPrefixes :
    visiblePrefixes (cons (some true) (const none)) = { log | log = [] ∨ log = [true] } := by
  have silentTail (n : Nat) : (take n (const (none : Option Bool))).filterMap id = [] := by
    have member : (take n (const none)).filterMap id ∈ visiblePrefixes (const (none : Option Bool)) :=
      ⟨n, rfl⟩
    rw [visiblePrefixes_of_silent _ (fun _ => rfl)] at member
    exact member
  ext log
  change (∃ n, (take n (cons (some true) (const none))).filterMap id = log) ↔ log = [] ∨ log = [true]
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr (congrArg (true :: ·) (silentTail n))
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

open Cslib.ωSequence in
example : (model false).Observes (some .emit)
    (.diverges {log | log = [] ∨ log = [true]}) := by
  refine ⟨.emit, Or.inl rfl, cons .emit (const .loop), cons (some true) (const none),
    rfl, ?_, emittedPrefixes⟩
  intro n
  cases n with
  | zero => exact Step.emit
  | succ _ => exact Step.spin

private theorem unmarkedSafe (p : Option State) : ¬ (model false).toHasOpSem.UBReachable p :=
  fun ⟨_, _, _, _, marked⟩ => Bool.noConfusion marked.1

example : (model false).completed id (some .start) = (model false).raw id (some .start) :=
  (model false).completed_of_safe id _ (unmarkedSafe _)

example : (model true).completed id (some .start) = Set.univ :=
  (model true).completed_of_ub id _
    ⟨.start, Or.inl rfl, .finished, .single ⟨some true, Step.finish⟩, rfl, rfl⟩

-- A terminal observation at a marked entry still takes the completion branch.
example : (model true).completed id (some .finished) = Set.univ :=
  (model true).completed_of_ub id _ ⟨.finished, Or.inl rfl, .finished, .refl, rfl, rfl⟩

example : (model true).completed id none = ∅ := by
  ext o
  simp [HasRuns.completed, HasOpSem.UBReachable, HasRuns.toHasOpSem, HasRuns.raw, HasRuns.Observes, model]

example : ¬ ((model false).raw id none).Nonempty :=
  fun h => by simpa [model] using ((model false).raw_nonempty_iff id none).mp h

private def cut : HasRuns (Option State) State Bool Bool where
  initial := (model false).initial
  semantics := {
    step := fun _ _ _ => False
    observe := fun _ _ => False
    blocked := fun _ => False
    ub := fun _ => True }

private theorem cutCoverage : RunCoverage (model false) cut id id (some .start) Eq where
  entry {source} admitted := ⟨source, admitted, rfl⟩
  run {_ target _} _ _ := Or.inl ⟨target, .refl, trivial⟩

example : (model false).completed id (some .start) ⊆ cut.completed id (some .start) :=
  cutCoverage.completed_le (fun reachable => (unmarkedSafe _ reachable).elim)

private theorem identityCoverage :
    RunCoverage (model false) (model false) id id (some .start) Eq where
  entry {source} admitted := ⟨source, admitted, rfl⟩
  run {_ _ obs} eq seen := Or.inr ⟨obs, eq ▸ seen, rfl⟩

example {Q : RunObservation Bool Bool → Prop}
    (holds : ∀ obs ∈ (model false).completed id (some .start), Q obs) :
    Q (.diverges {[]}) :=
  (identityCoverage.safe_transfer id (unmarkedSafe _) holds).2 _ ⟨.loop, Or.inr ⟨rfl, rfl⟩, silentLoop⟩

example : CompleteLattice (RunBehaviors (Option State) (RunObservation Bool Bool)) := inferInstance

example {family : Set (RunBehaviors Unit Nat)} : 0 ∈ (sInf family) () ↔ ∀ B ∈ family, 0 ∈ B () :=
  RunBehaviors.mem_sInf

example {family : Set (RunBehaviors Unit Nat)} : 0 ∈ (sSup family) () ↔ ∃ B ∈ family, 0 ∈ B () :=
  RunBehaviors.mem_sSup

-- Both programs can return true. Adding a second, silently looping entry
-- changes termination even though it contributes no finite may outcome.
private def mayModel (withLoop : Bool) : HasRuns Unit State Bool Bool where
  initial _ s := s = .finished ∨ (withLoop = true ∧ s = .loop)
  semantics := semantics false

private theorem reachableFromLoop {s : State}
    (reach : (semantics false).toWithUB.toOpSem.Reach .loop s) : s = .loop := by
  induction reach with
  | refl => rfl
  | tail _ edge ih =>
    obtain ⟨_, step⟩ := edge
    rw [ih] at step
    cases step
    rfl

example : (mayModel true).toHasOpSem.behaviors () ⊆ (mayModel false).toHasOpSem.behaviors () := by
  rintro outcome ⟨source, entry, last, reach, seen⟩
  rcases entry with rfl | ⟨_, rfl⟩
  · exact ⟨.finished, Or.inl rfl, last, reach, seen⟩
  · exact False.elim (State.noConfusion ((reachableFromLoop reach).symm.trans seen.1))

example : (mayModel false).toHasOpSem.May () (.returned true) :=
  ⟨.finished, Or.inl rfl, .finished, .refl, rfl, rfl⟩

example : (mayModel false).Terminates () := by
  rintro source (rfl | ⟨impossible, _⟩) diverges
  · exact OpSem.Normal.not_diverges finishEnd.1 diverges
  · exact Bool.noConfusion impossible

example : ¬ (mayModel true).Terminates () :=
  fun terminates => terminates (start := .loop) (Or.inr ⟨rfl, rfl⟩)
    (((semantics false).diverges_iff .loop).mpr ⟨{[]}, silentLoop⟩)

#print axioms RunSem.exists_observation
#print axioms HasRuns.raw_nonempty_iff
#print axioms HasRuns.terminates_iff
#print axioms RunCoverage.completed_le
#print axioms RunCoverage.safe_transfer
