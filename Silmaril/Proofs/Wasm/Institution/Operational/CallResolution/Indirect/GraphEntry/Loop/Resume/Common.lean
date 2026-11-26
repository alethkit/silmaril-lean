module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Thms
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs

open Execution.Runtime (Frame Value)
open CallContinuation
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked

theorem observation_iff {C : Type} {entry : Entry} {args : List Value} (render : State → C)
    (native : C → C → Prop) (caller site : List Value → C → Prop) {dst : C}
    (read : ∀ locals, Loop.Runs entry (entry.initial args) ⟨locals, .site⟩ →
      (Relation.ReflTransGen native (render ⟨locals, .site⟩) dst ↔ site locals dst)) :
    Observation entry args render caller native dst ↔ ObservationWithSite entry args render caller site dst := by
  apply or_congr Iff.rfl (or_congr Iff.rfl _)
  exact ⟨fun ⟨locals, run, after⟩ => ⟨locals, run, (read locals run).mp after⟩,
    fun ⟨locals, run, after⟩ => ⟨locals, run, (read locals run).mpr after⟩⟩

theorem edge_live {A : Type} {a b : Phase A} (move : Edge a b) : a.Live := by
  cases move <;> trivial

theorem preserve {A : Type} {entry : Entry} {a b : Phase A} (ready : Admitted entry a)
    (move : Edge a b) : Admitted entry b := by
  cases move <;> try exact ready
  case leaveArm => exact ready.1
  case write split step =>
    subst_vars
    obtain ⟨localsTyped, codeTyped⟩ := ready
    simp only [List.map_cons, Prefix.stackTypes, List.map_append, List.reverse_append] at codeTyped
    rename_i locals next saved value i rest
    have slot : entry.owner.localTypes[i.toNat]? = some value.type := by
      by_contra wrong
      simp [Locals.check, wrong] at codeTyped
    have localGuard : Locals.Admitted entry.owner.localTypes [] ⟨locals, [.value value, .set i]⟩ :=
      ⟨localsTyped, by simp [Locals.check, slot]⟩
    exact ⟨(Locals.closed localGuard step).1, by simpa [Prefix.stackTypes, Locals.check, slot] using codeTyped⟩

theorem empty_stack {A : Type} {entry : Entry} {locals stack : List Value}
    (ready : Admitted entry (A := A) (.write locals stack [])) : stack = [] := by
  have empty : (stack.map Value.type).reverse = [] := Option.some.inj ready.2
  simpa using empty

theorem deliver_admitted {A : Type} {entry : Entry} {program : Graph.Program} {call : Context.Invocation}
    (checked : call.Checked program) (locals : call.caller.locals.map Value.type = entry.owner.localTypes)
    (writes : Writes entry call.saved call.site.signature.results) {result : Nested.Result}
    (admitted : Graph.Admitted program call.callee (.done result)) (pending : List A) :
    Admitted entry (delivery call.caller call.saved writes.indices pending result) := by
  cases result with
  | trap => exact locals
  | values xs =>
    cases admitted with
    | done typed =>
      have types := typed.trans (congrArg Wasm.V1.FuncType.results (resolved_signature checked.resolved checked.found))
      exact ⟨locals, by simpa [Prefix.stackTypes, List.map_append, List.reverse_append, types] using writes.typed⟩

/-- Readback through a phase that has a distinct continuation at its final
state. No administrative step is inserted at the handoff. -/
theorem split_run {S C : Type} {edge : S → S → Prop} {native : C → C → Prop}
    (render : S → C) (live : S → Prop) (next : S → C → Prop) {start : S}
    (step : ∀ {a dst}, Relation.ReflTransGen edge start a → live a →
      (native (render a) dst ↔ ∃ b, edge a b ∧ dst = render b))
    (source : ∀ {a b}, Relation.ReflTransGen edge start a → edge a b → live a)
    (handoff : ∀ {a dst}, Relation.ReflTransGen edge start a → ¬ live a →
      (Relation.ReflTransGen native (render a) dst ↔ next a dst)) {dst : C} :
    Relation.ReflTransGen native (render start) dst ↔
      (∃ a, Relation.ReflTransGen edge start a ∧ dst = render a) ∨
      (∃ a, Relation.ReflTransGen edge start a ∧ ¬ live a ∧ next a dst) := by
  have sound {a} (walk : Relation.ReflTransGen edge start a) :
      Relation.ReflTransGen native (render start) (render a) := by
    induction walk with
    | refl => exact .refl
    | tail run move ih => exact ih.tail ((step run (source run move)).mpr ⟨_, move, rfl⟩)
  constructor
  · intro path
    induction path with
    | refl => exact .inl ⟨_, .refl, rfl⟩
    | tail _ move ih =>
      rcases ih with ⟨a, walk, rfl⟩ | ⟨a, walk, stop, tail⟩
      · by_cases continuing : live a
        · obtain ⟨b, edge, eq⟩ := (step walk continuing).mp move
          exact .inl ⟨b, walk.tail edge, eq⟩
        · exact .inr ⟨a, walk, continuing, (handoff walk continuing).mp (.single move)⟩
      · exact .inr ⟨a, walk, stop, (handoff walk stop).mp (((handoff walk stop).mpr tail).tail move)⟩
  · rintro (⟨a, walk, rfl⟩ | ⟨a, walk, stop, tail⟩)
    · exact sound walk
    · exact (sound walk).trans ((handoff walk stop).mpr tail)

theorem finish_iff {A C : Type} {entry : Entry} {program : Graph.Program}
    (render : Phase A → C) (caller : Graph.Phase → C) (native : C → C → Prop)
    {start : Phase A} (ready : Admitted entry start)
    (step : ∀ {a dst}, Admitted entry a → a.Live →
      (native (render a) dst ↔ ∃ b, Edge a b ∧ dst = render b))
    (callerRun : ∀ {locals trapped dst}, Admitted entry (.caller locals trapped : Phase A) →
      (Relation.ReflTransGen native (render (.caller locals trapped)) dst ↔
        ∃ phase, program.FrameRuns entry.address (entryPhase entry locals trapped) phase ∧ dst = caller phase))
    {dst : C} :
    Relation.ReflTransGen native (render start) dst ↔ Finish entry program render caller start dst := by
  have typed {a} (run : Runs start a) : Admitted entry a := by
    induction run with
    | refl => exact ready
    | tail _ move ih => exact preserve ih move
  let next : Phase A → C → Prop
    | .caller locals trapped, out =>
        ∃ phase, program.FrameRuns entry.address (entryPhase entry locals trapped) phase ∧ out = caller phase
    | _, _ => False
  refine (split_run render Phase.Live next (fun run live => step (typed run) live)
    (fun _ move => edge_live move) (fun {a dst} run stop => ?_)).trans (or_congr Iff.rfl ⟨?_, ?_⟩)
  · cases a with
    | caller => exact callerRun (typed run)
    | _ => exact (stop trivial).elim
  · rintro ⟨a, walk, stop, tail⟩
    cases a with
    | caller => exact ⟨_, _, walk, tail⟩
    | _ => exact (stop trivial).elim
  · rintro ⟨locals, trapped, walk, tail⟩
    exact ⟨.caller locals trapped, walk, id, tail⟩

private theorem reachable {program : Graph.Program} {call : Context.Invocation}
    (checked : call.Checked program) {phase : Graph.Phase}
    (run : program.FrameRuns call.address call.entered phase) :
    phase.LabelOutcome ∨ ∃ result, phase = .done result := by
  induction run with
  | refl => exact .inl trivial
  | tail _ move ih =>
    rcases ih with live | ⟨_, rfl⟩
    · exact Context.entered_frame_edge checked.found live move
    · cases (program.frameEdge_iff checked.found).mp move

theorem callee_iff {C : Type} {program : Graph.Program} {call : Context.Invocation}
    (checked : call.Checked program) (render : Graph.Phase → C) (native : C → C → Prop)
    (finish : Nested.Result → C → Prop)
    (step : ∀ {a dst}, Graph.Admitted program call.callee a → a.LabelOutcome →
      (native (render a) dst ↔ ∃ b, program.FrameEdge call.address a b ∧ dst = render b))
    (handoff : ∀ {r dst}, Graph.Admitted program call.callee (.done r) →
      (Relation.ReflTransGen native (render (.done r)) dst ↔ finish r dst)) {dst : C} :
    Relation.ReflTransGen native (render call.entered) dst ↔ CalleeFinish program call render finish dst := by
  have typed {a} (run : program.FrameRuns call.address call.entered a) : Graph.Admitted program call.callee a :=
    program.frame_admitted_run checked.graph checked.found (Context.entered_admitted checked) run
  let next : Graph.Phase → C → Prop
    | .done r, out => finish r out
    | _, _ => False
  refine (split_run render Graph.Phase.LabelOutcome next (fun run live => step (typed run) live)
    (fun run move => ?_) (fun {a dst} run stop => ?_)).trans (or_congr Iff.rfl ⟨?_, ?_⟩)
  · rcases reachable checked run with live | ⟨_, rfl⟩
    · exact live
    · cases (program.frameEdge_iff checked.found).mp move
  · rcases reachable checked run with live | ⟨_, rfl⟩
    · exact (stop live).elim
    · exact handoff (typed run)
  · rintro ⟨a, run, stop, path⟩
    rcases reachable checked run with live | ⟨_, rfl⟩
    · exact (stop live).elim
    · exact ⟨_, run, path⟩
  · rintro ⟨r, run, path⟩
    exact ⟨.done r, run, id, path⟩

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.GraphEntry.Loop.Resume.Proofs
