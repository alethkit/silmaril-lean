module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Common

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs

open CallContinuation
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed
open Execution.Runtime (Frame Value)

private theorem plug_admitted {program : Graph.Program} {fn : Graph.Function}
    {locals : List Value} {body : Graph.Body} (blocks : List Block) (saved : List Value)
    (fallthrough : List NumType) (enclosing : Graph.EnclosingLabels)
    (checked : Block.check fn blocks saved fallthrough enclosing = true)
    (inside : let types := Block.context blocks fallthrough enclosing
      Graph.AdmittedAt program fn types.1 types.2 (.label locals body)) :
    Graph.AdmittedAt program fn fallthrough enclosing (.label locals (Block.plug blocks saved body)) := by
  induction blocks generalizing saved fallthrough enclosing with
  | nil => exact inside
  | cons block rest ih =>
    have ⟨inner, tail⟩ := Bool.and_eq_true_iff.mp checked
    exact .block (ih [] block.result.toList (fallthrough :: enclosing) inner inside) tail

theorem resume_admitted {cont : Continuation} {program : Graph.Program} {caller : Frame}
    {saved : List Value} {results : List NumType} {result : Nested.Result}
    (checked : cont.Checked program caller saved results)
    (typed : match result with | .values xs => xs.map Value.type = results | .trap => True) :
    Graph.Admitted program cont.owner (cont.resume caller saved result) := by
  have localBody : Graph.AdmittedAt program cont.owner cont.fallthrough cont.enclosing
      (.label caller.locals (cont.deliver saved result)) := by
    cases result with
    | trap => exact .trapped checked.locals_typed
    | values xs =>
      apply Graph.AdmittedAt.running checked.locals_typed
      simpa only [Graph.Function.WellTyped, Prefix.stackTypes, List.map_append, List.reverse_append, typed]
        using checked.tail_typed
  exact plug_admitted cont.blocks cont.owner.initial cont.owner.declaration.results [] checked.block_typed localBody

private def Ready (program : Graph.Program) (call : Invocation) (cont : Continuation) : Phase → Prop
  | .callee a => Graph.Admitted program call.callee a ∧ Context.Proofs.Entered a
  | .caller a => Graph.Admitted program cont.owner a ∧ Context.Proofs.Entered a

private theorem handoff_ready {cont : Continuation} {program : Graph.Program} {call : Invocation}
    (checked : call.Checked program)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {result : Nested.Result} (ready : Graph.Admitted program call.callee (.done result)) :
    Graph.Admitted program cont.owner (cont.resume call.caller call.saved result) := by
  apply resume_admitted continuation
  have sig := resolved_signature checked.resolved checked.found
  cases ready with
  | done typed =>
    cases result with
    | trap => trivial
    | values xs =>
      exact typed.trans (congrArg Wasm.V1.FuncType.results sig)

private theorem in_caller_label (cont : Continuation) (caller : Frame) (saved : List Value)
    (result : Nested.Result) : (cont.resume caller saved result).LabelOutcome := by
  cases result <;> trivial

private theorem preserve {program : Graph.Program} {cont : Continuation} {call : Invocation}
    (checked : call.Checked program)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    {a b : Phase} (ready : Ready program call cont a) (move : Edge program call cont a b) :
    Ready program call cont b := by
  cases move with
  | callee live move =>
    exact ⟨program.frame_admitted_step checked.graph checked.found ready.1 move,
      Context.Proofs.step_entered checked live move⟩
  | resume move =>
    exact ⟨program.frame_admitted_step checked.graph continuation.found
      (handoff_ready checked continuation ready.1) move,
      Context.Proofs.frame_entered continuation.found (in_caller_label _ _ _ _) move⟩
  | caller move =>
    rcases ready.2 with live | ⟨result, rfl⟩
    · exact ⟨program.frame_admitted_step checked.graph continuation.found ready.1 move,
        Context.Proofs.frame_entered continuation.found live move⟩
    · cases (program.frameEdge_iff continuation.found).mp move

private theorem entered_excludes_calls {a : Graph.Phase} (ready : Context.Proofs.Entered a)
    (args : List Value) : a ≠ .call args ∧ a ≠ .invoke args := by
  constructor <;> rintro rfl
  all_goals
    rcases ready with impossible | ⟨result, impossible⟩
    · exact impossible
    · cases impossible

theorem entered_run_iff {C : Type} {program : Graph.Program} {cont : Continuation} {call : Invocation}
    (checked : call.Checked program)
    (continuation : cont.Checked program call.caller call.saved call.site.signature.results)
    (render : Phase → C) (native : C → C → Prop)
    (childStep : ∀ {a b}, Graph.Admitted program call.callee a → a.LabelOutcome →
      (native (render (.callee a)) b ↔ ∃ out, program.FrameEdge call.address a out ∧ b = render (.callee out)))
    (callerStep : ∀ {a b}, Graph.Admitted program cont.owner a → (∀ args, a ≠ .call args ∧ a ≠ .invoke args) →
      (native (render (.caller a)) b ↔ ∃ out, program.FrameEdge cont.address a out ∧ b = render (.caller out)))
    (handoff : ∀ result, render (.callee (.done result)) = render (.caller (cont.resume call.caller call.saved result)))
    {b : C} :
    Relation.ReflTransGen native (render (.callee call.entered)) b ↔
      ∃ out, Runs program call cont (.callee call.entered) out ∧ b = render out := by
  have one {a b} (ready : Ready program call cont a) :
      native (render a) b ↔ ∃ out, Edge program call cont a out ∧ b = render out := by
    cases a with
    | callee a =>
      rcases ready.2 with live | ⟨result, rfl⟩
      · refine (childStep ready.1 live).trans ⟨?_, ?_⟩
        · rintro ⟨out, move, eq⟩
          exact ⟨_, .callee live move, eq⟩
        · rintro ⟨out, move, eq⟩
          cases move with
          | callee _ move => exact ⟨_, move, eq⟩
          | resume => cases live
      · rw [handoff result]
        refine (callerStep (handoff_ready checked continuation ready.1)
          (entered_excludes_calls (.inl (in_caller_label _ _ _ _)))).trans ⟨?_, ?_⟩
        · rintro ⟨out, move, eq⟩
          exact ⟨_, .resume move, eq⟩
        · rintro ⟨out, move, eq⟩
          cases move with
          | callee live => cases live
          | resume move => exact ⟨_, move, eq⟩
    | caller a =>
      refine (callerStep ready.1 (entered_excludes_calls ready.2)).trans ⟨?_, ?_⟩
      · rintro ⟨out, move, eq⟩
        exact ⟨_, .caller move, eq⟩
      · rintro ⟨out, move, eq⟩
        cases move with
        | caller move => exact ⟨_, move, eq⟩
  have ready : Ready program call cont (.callee call.entered) :=
    ⟨Context.entered_admitted checked, .inl trivial⟩
  refine (Context.Proofs.lift_runs (Ready program call cont) render
    (fun h move => preserve checked continuation h move) (fun h => one h) ready).trans ⟨?_, ?_⟩
  · rintro ⟨out, path, _, eq⟩
    exact ⟨out, path, eq⟩
  · rintro ⟨out, path, eq⟩
    have valid : Ready program call cont out := by
      clear eq
      induction path with
      | refl => exact ready
      | tail _ move ih => exact preserve checked continuation ih move
    exact ⟨out, path, valid, eq⟩

theorem of_callee_run {program : Graph.Program} {cont : Continuation} {call : Invocation}
    (checked : call.Checked program) {phase : Graph.Phase}
    (path : program.FrameRuns call.address call.entered phase) :
    Runs program call cont (.callee call.entered) (.callee phase) := by
  suffices Runs program call cont (.callee call.entered) (.callee phase) ∧ Context.Proofs.Entered phase
    from this.1
  induction path with
  | refl => exact ⟨.refl, .inl trivial⟩
  | tail _ move ih =>
    rcases ih with ⟨steps, live | ⟨result, rfl⟩⟩
    · exact ⟨steps.tail (.callee live move), Context.Proofs.step_entered checked live move⟩
    · cases (program.frameEdge_iff checked.found).mp move

theorem prefix_run_iff {C : Type} {native : C → C → Prop} (before : List C) (entry : C) {dst : C}
    (chain : (before ++ [entry]).IsChain (fun a b => ∀ out, native a out ↔ out = b)) :
    Relation.ReflTransGen native (before.headD entry) dst ↔
      dst ∈ before ∨ Relation.ReflTransGen native entry dst := by
  induction before with
  | nil => simp
  | cons first rest ih =>
    have chain' : (first :: (rest ++ [entry])).IsChain
        (fun a b => ∀ out, native a out ↔ out = b) := chain
    have pair : ∀ out, native first out ↔ out = rest.headD entry := by
      cases rest <;> exact (List.isChain_cons_cons.mp chain').1
    have restChain : (rest ++ [entry]).IsChain (fun a b => ∀ out, native a out ↔ out = b) :=
      by cases rest <;> exact (List.isChain_cons_cons.mp chain').2
    constructor
    · intro path
      rcases path.cases_head with eq | ⟨next, step, tail⟩
      · exact .inl (List.mem_cons.mpr (.inl eq.symm))
      · obtain rfl := (pair next).mp step
        rcases (ih restChain).mp tail with earlier | later
        · exact .inl (List.mem_cons.mpr (.inr earlier))
        · exact .inr later
    · intro h
      have move := (pair (rest.headD entry)).mpr rfl
      rcases h with mem | run
      · rcases List.mem_cons.mp mem with rfl | mem
        · exact .refl
        · exact ((ih restChain).mpr (.inl mem)).head move
      · exact ((ih restChain).mpr (.inr run)).head move

theorem map_chain {C D : Type} {R : C → C → Prop} {S : D → D → Prop}
    (f : C → D) {xs : List C}
    (chain : xs.IsChain R) (lift : ∀ a ∈ xs.dropLast, ∀ b, R a b → S (f a) (f b)) :
    (xs.map f).IsChain S := by
  induction chain with
  | nil => exact .nil
  | singleton => exact .singleton _
  | cons_cons head tail ih =>
    apply List.isChain_cons_cons.mpr
    refine ⟨lift _ (by simp) _ head, ih ?_⟩
    intro a mem b step
    exact lift a (by simp [mem]) b step

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Resume.Proofs
