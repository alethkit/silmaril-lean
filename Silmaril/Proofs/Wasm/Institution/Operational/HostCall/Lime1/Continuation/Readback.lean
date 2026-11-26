module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Preservation
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {results : List NumType} {bytes : ByteArray} {dst : Config H}

private theorem withoutCallout {src : Config H} (absent : decompose? src = none) :
    Step host src dst ↔ Internal src dst := by
  apply Step.internal_iff_of_not_callout
  intro call located
  have found := exists_callout_iff.mp ⟨call, located⟩
  simp [absent] at found

private theorem underLabel {body : List Admin}
    (stays : ∀ out, ¬ PureStep active.module.types [.label results.length [] body] out)
    (move : Internal ⟨mem.store bytes, outer, entered results.length active body⟩ dst) :
    ∃ mid, Internal ⟨mem.store bytes, active, body⟩ mid ∧ dst =
      ⟨mid.store, outer, entered results.length mid.frame mid.code⟩ := by
  rcases Computed.lime_body_step_cases move with inside | ⟨out, exiting, _⟩
  · exact inside
  · exact (stays out exiting).elim

private theorem closeLabel {r : Result}
    (move : Internal ⟨mem.store bytes, outer, entered results.length active (result r)⟩ dst) :
    dst = ⟨mem.store bytes, outer, [.frame results.length active (result r)]⟩ := by
  cases r with
  | values vs =>
    rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .values vs) inside).elim
    · rw [Nested.lime_label_result (r := .values vs) pop]
      rfl
  | trap =>
    rcases Computed.lime_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · rw [Nested.lime_label_result (r := .trap) pop]
      rfl

private theorem located {site : Site H} {args saved : List Value} {ops : List (Op H)}
    (allocated : site.Allocated base) (typed : site.Arguments args) :
    CalloutAt (render mem outer active results.length ⟨bytes, .invoke saved site args ops⟩)
      (site.callout (invokeContext results.length active saved ops) args) :=
  ⟨rfl, allocated, by simpa [Site.callout] using congrArg List.length typed⟩

private theorem invoke_read {saved args : List Value} {site : Site H} {ops : List (Op H)}
    (ready : Ready mem host active results (.invoke saved site args ops)) (live : mem.Live bytes)
    (move : Step host (render mem outer active results.length ⟨bytes, .invoke saved site args ops⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .invoke saved site args ops⟩ next ∧
      dst = render mem outer active results.length next := by
  obtain ⟨allocated, typed, contract, _, _⟩ := ready
  have exactStep := Site.step_iff (dst := dst) (outer := outer)
    (context := invokeContext results.length active saved ops) allocated contract live typed
  rcases exactStep.mp move with ⟨next, out, nLive, nTyped, answer, rfl⟩ | ⟨diverges, rfl⟩
  · cases out with
    | values vs => exact ⟨⟨next, .source (saved ++ vs) ops⟩, .returned nLive nTyped answer,
        by simp [render, Phase.renderCode, invokeContext, entered, Execution.Runtime.EvalCtx.plug, result,
          List.append_assoc, values]⟩
        | trap => exact ⟨⟨next, .trapped saved (code ops)⟩, .trapped nLive answer,
        by simp [render, Phase.renderCode, invokeContext, entered, Execution.Runtime.EvalCtx.plug, result, values]⟩
  · exact ⟨_, .diverged diverges, rfl⟩

private theorem source_read {stack : List Value} {ops : List (Op H)}
    (ready : Ready mem host active results (.source stack ops))
    (move : Internal (render mem outer active results.length ⟨bytes, .source stack ops⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .source stack ops⟩ next ∧
      dst = render mem outer active results.length next := by
  cases ops with
  | nil =>
    have move' : Internal ⟨mem.store bytes, outer, entered results.length active (result (.values stack))⟩ dst := by
      simpa [render, Phase.renderCode, code, expression, result] using move
    exact ⟨⟨bytes, .frameResult (.values stack)⟩, .labelResult, closeLabel (r := .values stack) move'⟩
  | cons op ops =>
    have stay (out : List Admin) : ¬ PureStep active.module.types
        [.label results.length [] (values stack ++ .source op.instr :: code ops)] out :=
      Computed.lime_label_stays (by cases op <;> rfl) (by cases op <;> simp [Op.instr])
        (by cases op <;> simp [Op.instr]) (by simp)
    obtain ⟨mid, inside, rfl⟩ := underLabel stay move
    cases op with
    | get i =>
      obtain ⟨type, lookup, _⟩ := checked_get ready.1
      rw [List.getElem?_map] at lookup
      obtain ⟨v, found, _⟩ := Option.map_eq_some_iff.mp lookup
      obtain rfl := (Computed.lime_local_get_iff (stack := stack) (rest := code ops) found).mp inside
      exact ⟨⟨bytes, .source (stack ++ [v]) ops⟩, .get found,
        by simp [render, Phase.renderCode, List.append_assoc, values]⟩
    | drop =>
      obtain ⟨savedTypes, type, split, _⟩ := checked_drop ready.1
      obtain ⟨kept, dropped, rfl, _, droppedType⟩ := List.map_eq_append_iff.mp split
      obtain ⟨v, rest, rfl, _, restNil⟩ := List.map_eq_cons_iff.mp droppedType
      obtain rfl := List.map_eq_nil_iff.mp restNil
      obtain rfl := (Computed.lime_drop_iff (stack := kept) (v := v) (rest := code ops)).mp inside
      exact ⟨⟨bytes, .source kept ops⟩, .drop, rfl⟩
    | call i site =>
      obtain ⟨_, split, resolved, _, _⟩ := checked_call ready.1
      obtain ⟨saved, args, rfl, _, typed⟩ := List.map_eq_append_iff.mp split
      obtain rfl := (Computed.lime_direct_call_iff (stack := saved ++ args) (tail := code ops) resolved).mp inside
      exact ⟨⟨bytes, .invoke saved site args ops⟩, .resolve typed,
        by simp [render, Phase.renderCode, invokeContext, entered, Execution.Runtime.EvalCtx.plug,
          List.append_assoc, values]⟩

private theorem trap_read {stack : List Value} {rest : List Admin}
    (move : Internal (render mem outer active results.length ⟨bytes, .trapped stack rest⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .trapped stack rest⟩ next ∧
      dst = render mem outer active results.length next := by
  by_cases someCode : stack ≠ [] ∨ rest ≠ []
  · have stays (out : List Admin) :
        ¬ PureStep active.module.types [.label results.length [] (values stack ++ .trap :: rest)] out :=
      Computed.lime_label_stays rfl (by simp) (by simp) (fun _ => someCode)
    obtain ⟨mid, inside, rfl⟩ := underLabel stays move
    have erase := Computed.lime_trap_front_iff (s := mem.store bytes) (f := active) (dst := mid)
      (stack := stack) (tail := rest)
    obtain ⟨kept, removed, cut, next, split, suffix, activeTrap, rfl⟩ := erase.mp inside
    exact ⟨⟨bytes, .trapped kept next⟩, .erase split suffix activeTrap, rfl⟩
  · obtain ⟨emptyStack, emptyRest⟩ := not_or.mp someCode
    have stackNil : stack = [] := not_not.mp emptyStack
    have restNil : rest = [] := not_not.mp emptyRest
    subst stack rest
    exact ⟨⟨bytes, .frameResult .trap⟩, .labelTrap, closeLabel (r := .trap) move⟩

private theorem frame_read {r : Result}
    (move : Internal (render mem outer active results.length ⟨bytes, .frameResult r⟩) dst) :
    dst = render mem outer active results.length ⟨bytes, .done r⟩ := by
  cases r with
  | values vs => exact Nested.lime_frame_result (r := .values vs) move
  | trap => exact Nested.lime_frame_result (r := .trap) move

private theorem read {a : State H} (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes)
    (move : Step host (render mem outer active results.length a) dst) :
    ∃ next, Edge mem host active a next ∧ dst = render mem outer active results.length next := by
  rcases a with ⟨bytes, phase⟩
  cases phase with
  | source stack ops =>
    have absent : decompose? (render mem outer active results.length ⟨bytes, .source stack ops⟩) = none := by
      cases ops with
      | nil => simp [decompose?, render, Phase.renderCode, entered, code, expression]
      | cons op ops => cases op <;> simp [decompose?, render, Phase.renderCode, entered, code, Op.instr, expression, asValue?]
    exact source_read ready ((withoutCallout absent).mp move)
  | invoke saved site args ops => exact invoke_read ready live move
  | trapped stack rest =>
    have absent : decompose? (render mem outer active results.length ⟨bytes, .trapped stack rest⟩) = none := by
      simp [decompose?, render, Phase.renderCode, entered]
    exact trap_read ((withoutCallout absent).mp move)
  | frameResult out =>
    have absent : decompose? (render mem outer active results.length ⟨bytes, .frameResult out⟩) = none := by
      cases out <;> simp [decompose?, render, Phase.renderCode, result]
    exact ⟨⟨bytes, .done out⟩, .frameDone, frame_read ((withoutCallout absent).mp move)⟩
  | done out =>
    have absent : decompose? (render mem outer active results.length ⟨bytes, .done out⟩) = none := by
      cases out <;> simp [decompose?, render, Phase.renderCode, result]
    have internal := (withoutCallout absent).mp move
    cases out with
    | values vs => exact (Nested.lime_result_stuck (r := .values vs) internal).elim
    | trap => exact (Nested.lime_result_stuck (r := .trap) internal).elim

private theorem sound {a b : State H} (ready : Ready mem host active results a.phase) (edge : Edge mem host active a b) :
    Step host (render mem outer active results.length a) (render mem outer active results.length b) := by
  cases edge with
  | @get bytes stack index v ops found =>
    have get := (Computed.lime_local_get_iff (s := mem.store bytes) (stack := stack) (rest := code ops) found).mpr rfl
    have move := Step.frame (.label get results.length []) results.length outer
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, entered, code, Op.instr, expression, values, List.append_assoc] using move
  | @drop bytes stack v ops =>
    have drop := (Computed.lime_drop_iff (s := mem.store bytes) (f := active) (stack := stack)
      (v := v) (rest := code ops)).mpr rfl
    exact Step.of_internal (.frame (.label drop results.length []) results.length outer)
  | @resolve bytes saved args index site ops typed =>
    obtain ⟨_, _, resolved, _, _⟩ := checked_call ready.1
    have call := (Computed.lime_direct_call_iff (s := mem.store bytes) (stack := saved ++ args)
      (tail := code ops) resolved).mpr rfl
    have move := Step.frame (.label call results.length []) results.length outer
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [render, Phase.renderCode, entered, invokeContext, Execution.Runtime.EvalCtx.plug,
      code, Op.instr, expression, List.append_assoc, values] using move
  | @returned bytes next saved site args ops vs _ _ answer =>
    have atHost := located (mem := mem) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.1 ready.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, render, Phase.renderCode, entered, invokeContext, Site.callout,
      Execution.Runtime.Callout.fill, Execution.Runtime.EvalCtx.plug, result, List.append_assoc, values] using move
  | @trapped bytes next saved site args ops _ answer =>
    have atHost := located (mem := mem) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.1 ready.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, render, Phase.renderCode, entered, invokeContext, Site.callout,
      Execution.Runtime.Callout.fill, Execution.Runtime.EvalCtx.plug, result, values] using move
  | diverged answer => exact Step.callout_diverged (located (results := results) ready.1 ready.2.1) answer
  | @erase bytes stack kept removed before cut rest split suffix activeTrap =>
    have move : Internal ⟨mem.store bytes, active, values stack ++ .trap :: before⟩
        ⟨mem.store bytes, active, values kept ++ .trap :: rest⟩ :=
      Computed.lime_trap_front_iff.mpr ⟨kept, removed, cut, rest, split, suffix, activeTrap, rfl⟩
    exact Step.of_internal (.frame (.label move results.length []) results.length outer)
  | labelTrap => exact .frame (.pure _ _ (.labelTrap results.length [])) results.length outer
  | @labelResult bytes stack =>
    have move := Step.frame (.pure (host := host) (mem.store bytes) active (.labelDone results.length [] stack))
      results.length outer
    simpa [render, Phase.renderCode, entered, code, expression, result] using move
  | @frameDone _ out =>
    cases out with
    | trap => exact .pure _ _ (.frameTrap _ active)
    | values vs =>
      exact .pure _ _ (.frameDone _ active vs (by simpa using congrArg List.length ready))

theorem step_iff {a : State H} (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Step host (render mem outer active results.length a) dst ↔
      ∃ next, Edge mem host active a next ∧ dst = render mem outer active results.length next := by
  refine ⟨read ready live, ?_⟩
  rintro ⟨_, edge, rfl⟩
  exact sound ready edge

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
