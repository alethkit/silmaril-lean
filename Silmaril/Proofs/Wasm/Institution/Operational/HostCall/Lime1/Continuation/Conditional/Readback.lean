module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional.Defs
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional.Proofs

open Execution.Runtime (EvalCtx Frame Value)
open Wasm.Lime1.Execution
open CallContinuation.OuterCall

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {results : List NumType} {bytes : ByteArray} {dst : Config H}
  {choice : Choice H} {saved : List Value} {guard : BitVec 32}

theorem start_ready {plan : Plan H} (checked : plan.Checked base active.module
    (active.locals.map Value.type) results (saved.map Value.type))
    (contract : plan.Contract mem host) :
    Ready mem host active results (plan.start saved guard) := by
  cases plan with
  | straight ops =>
    refine ⟨?_, contract⟩
    rw [List.map_append]
    exact checked
  | if_ choice => exact ⟨checked, contract⟩

private theorem selected_ready (checked : choice.Checked base active.module (active.locals.map Value.type)
    results (saved.map Value.type)) (contract : choice.Contract mem host) :
    Continuation.Ready mem host active [choice.type] (.source [] (choice.selected guard)) := by
  by_cases zero : guard = 0
  · rw [Choice.selected, ite_eq_left zero]
    exact ⟨checked.elseArm, contract.2.1⟩
  · rw [Choice.selected, ite_eq_right zero]
    exact ⟨checked.thenArm, contract.1⟩

private theorem arm_ready {a b : Continuation.State H} (move : Continuation.Edge mem host active a b)
    (ready : Ready mem host active results (.arm saved choice a.phase)) (live : mem.Live a.bytes) :
    Ready mem host active results (afterArm saved choice b.phase) ∧ mem.Live b.bytes := by
  obtain ⟨inside, body, join, joinContract⟩ := ready
  obtain ⟨next, nextLive⟩ := Continuation.preserves (results := [choice.type]) move body live
  refine ⟨?_, nextLive⟩
  cases move with
  | labelResult =>
    have typed : _ = [choice.type] := next
    exact ⟨by simpa only [List.map_append, typed] using join, joinContract⟩
  | labelTrap => trivial
  | frameDone => exact inside.elim
  | _ => exact ⟨trivial, next, join, joinContract⟩

theorem preserves {a b : State H} (move : Edge mem host active a b)
    (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Ready mem host active results b.phase ∧ mem.Live b.bytes := by
  cases move with
  | select => exact ⟨ready, live⟩
  | enter => exact ⟨⟨trivial, selected_ready ready.1 ready.2, ready.1.tail, ready.2.2.2⟩, live⟩
  | arm move => exact arm_ready move ready live
  | tail move => exact Continuation.preserves move ready live

private theorem deliver_code {a b : Continuation.State H} (move : Continuation.Edge mem host active a b)
    (inside : a.phase.InLabel) :
    b.phase.renderIn (some (armContext results.length saved choice)) 1 active =
      (afterArm saved choice b.phase).renderCode results.length active := by
  cases move with
  | labelResult =>
    simp [afterArm, Phase.renderCode, Continuation.Phase.renderCode, Continuation.Phase.renderIn,
      armContext, framed, frameContext, EvalCtx.plug, result, code, expression, values, List.append_assoc]
  | labelTrap =>
    simp [afterArm, Phase.renderCode, Continuation.Phase.renderCode, Continuation.Phase.renderIn,
      armContext, framed, frameContext, EvalCtx.plug, result, values]
  | frameDone => exact inside.elim
  | _ => rfl

private theorem function_iff {head : Admin} {stack : List Value} {rest out : List Admin}
    (nonvalue : asValue? head = none) (notBranch : ∀ i, head ≠ .source (.br i))
    (notReturn : head ≠ .source .return_) (notTrap : head ≠ .trap)
    (noCallout : decompose? (⟨mem.store bytes, outer,
      entered results.length active (values stack ++ head :: rest)⟩ : Config H) = none)
    (step : ∀ {mid}, Internal ⟨mem.store bytes, active, values stack ++ head :: rest⟩ mid ↔
      mid = ⟨mem.store bytes, active, out⟩) :
    Step host ⟨mem.store bytes, outer, entered results.length active (values stack ++ head :: rest)⟩ dst ↔
      dst = ⟨mem.store bytes, outer, entered results.length active out⟩ := by
  have absent : ∀ c, ¬ CalloutAt (⟨mem.store bytes, outer,
      entered results.length active (values stack ++ head :: rest)⟩ : Config H) c := by
    intro call located
    have found := exists_callout_iff.mp ⟨call, located⟩
    simp [noCallout] at found
  rw [Step.internal_iff_of_not_callout absent]
  constructor
  · intro move
    rcases Computed.lime_body_step_cases move with ⟨mid, inside, rfl⟩ | ⟨_, pop, _⟩
    · obtain rfl := step.mp inside
      rfl
    · exact (Computed.lime_label_stays nonvalue notBranch notReturn (fun h => (notTrap h).elim) pop).elim
  · rintro rfl
    exact .frame (.label (step.mpr rfl) results.length []) results.length outer

private theorem test_iff :
    Step host (render mem outer active results.length ⟨bytes, .test saved guard choice⟩) dst ↔
      dst = render mem outer active results.length ⟨bytes, .block saved guard choice⟩ := by
  apply function_iff (stack := saved ++ [i32 guard]) (head := .source choice.instr) (rest := code choice.tail)
  · rfl
  · simp [Choice.instr]
  · simp [Choice.instr]
  · simp
  · simp [decompose?, entered, Choice.instr, asValue?]
  · intro mid
    change Step CallFrame.limeNoHost _ _ ↔ _
    have select := Computed.lime_if_iff (s := mem.store bytes) (f := active) (saved := saved)
      (condition := guard) (bt := .value choice.type) (thenBody := choice.thenOps.map Op.instr)
      (elseBody := choice.elseOps.map Op.instr) (rest := code choice.tail) (dst := mid)
    by_cases zero : guard = 0
    · simpa only [Choice.instr, Choice.selected, ite_eq_left zero, i32] using select
    · simpa only [Choice.instr, Choice.selected, ite_eq_right zero, i32] using select

private theorem enter_iff :
    Step host (render mem outer active results.length ⟨bytes, .block saved guard choice⟩) dst ↔
      dst = render mem outer active results.length ⟨bytes, .arm saved choice (.source [] (choice.selected guard))⟩ := by
  apply function_iff (stack := saved)
    (head := .source (.block (.value choice.type) ((choice.selected guard).map Op.instr))) (rest := code choice.tail)
  · rfl
  · simp
  · simp
  · simp
  · simp [decompose?, entered, asValue?]
  · intro mid
    change Step CallFrame.limeNoHost _ _ ↔ _
    simpa [Blocks.limeType, armContext, EvalCtx.plug, code, values, List.append_assoc] using
      (Computed.lime_block_iff (s := mem.store bytes) (f := active) (result := some choice.type)
        (stack := saved) (body := (choice.selected guard).map Op.instr) (rest := code choice.tail) (dst := mid))

private theorem read {a : State H} (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes)
    (step : Step host (render mem outer active results.length a) dst) :
    ∃ next, Edge mem host active a next ∧ dst = render mem outer active results.length next := by
  rcases a with ⟨bytes, phase⟩
  cases phase with
  | test saved guard choice => exact ⟨_, .select, test_iff.mp step⟩
  | block saved guard choice => exact ⟨_, .enter, enter_iff.mp step⟩
  | arm saved choice phase =>
    have steps := Continuation.label_step_iff (mem := mem) (host := host) (outer := outer) (active := active)
      (results := [choice.type]) (context := armContext results.length saved choice)
      (a := ⟨bytes, phase⟩) (dst := dst) ready.1 ready.2.1 live
    obtain ⟨next, move, rfl⟩ := steps.mp step
    refine ⟨⟨next.bytes, afterArm saved choice next.phase⟩, .arm move, ?_⟩
    exact congrArg (fun code => (⟨mem.store next.bytes, outer, code⟩ : Config H))
      (deliver_code (saved := saved) (choice := choice) (results := results) move ready.1)
  | tail phase =>
    have steps := Continuation.step_iff (mem := mem) (host := host) (outer := outer) (active := active)
      (results := results) (a := ⟨bytes, phase⟩) (dst := dst) ready live
    obtain ⟨next, move, eq⟩ := steps.mp step
    exact ⟨⟨next.bytes, .tail next.phase⟩, .tail move, eq⟩

private theorem sound {a b : State H} (move : Edge mem host active a b)
    (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Step host (render mem outer active results.length a) (render mem outer active results.length b) := by
  cases move with
  | select => exact test_iff.mpr rfl
  | enter => exact enter_iff.mpr rfl
  | @arm bytes next saved choice a b move =>
    have steps := Continuation.label_step_iff (mem := mem) (host := host) (outer := outer) (active := active)
      (results := [choice.type]) (context := armContext results.length saved choice) (a := ⟨bytes, a⟩)
      (dst := render mem outer active results.length ⟨next, afterArm saved choice b⟩) ready.1 ready.2.1 live
    refine steps.mpr ⟨_, move, ?_⟩
    exact congrArg (fun code => (⟨mem.store next, outer, code⟩ : Config H))
      (deliver_code (saved := saved) (choice := choice) (results := results) move ready.1).symm
  | @tail bytes next a b move =>
    exact (Continuation.step_iff (mem := mem) (host := host) (outer := outer) (active := active) (results := results)
      (a := ⟨bytes, a⟩) (dst := render mem outer active results.length ⟨next, .tail b⟩) ready live).mpr ⟨_, move, rfl⟩

theorem step_iff {a : State H} (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Step host (render mem outer active results.length a) dst ↔
      ∃ next, Edge mem host active a next ∧ dst = render mem outer active results.length next := by
  refine ⟨read ready live, ?_⟩
  rintro ⟨_, move, rfl⟩
  exact sound move ready live

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Conditional.Proofs
