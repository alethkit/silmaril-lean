module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Preservation
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs

open Execution.Runtime (EvalCtx Frame Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {scope : Option LabelContext} {results : List NumType} {bytes : ByteArray} {dst : Config H}

private theorem withoutCallout {src : Config H} (absent : decompose? src = none) :
    Step host src dst ↔ Internal src dst := by
  apply Step.internal_iff_of_not_callout
  intro call located
  have found := exists_callout_iff.mp ⟨call, located⟩
  simp [absent] at found

@[simp] private theorem framed_none (arity : Nat) (active : Frame) (body : List Admin) :
    framed none arity active body = [.frame arity active body] :=
  rfl

@[simp] private theorem framed_some (context : LabelContext) (arity : Nat) (active : Frame) (body : List Admin) :
    framed (some context) arity active body =
      [.frame context.arity active [.label context.arity [] (values context.saved ++ body ++ context.tail)]] :=
  rfl

private theorem plug_invoke {saved : List Value} {ops : List (Op H)} {body : List Admin} :
    (invokeContextIn scope results.length active saved ops).plug value body =
      framed scope results.length active [.label results.length [] (values saved ++ body ++ code ops)] := by
  rw [invokeContextIn, EvalCtx.plug_comp]
  rfl

private theorem framed_step {s s' : Store H} {body next : List Admin}
    (move : Step host ⟨s, active, body⟩ ⟨s', active, next⟩) :
    Step host ⟨s, outer, framed scope results.length active body⟩
      ⟨s', outer, framed scope results.length active next⟩ :=
  Step.plug_activeFrame (frameContext scope results.length active) outer (by cases scope <;> exact move)

private theorem body_cases {body : List Admin}
    (move : Internal ⟨mem.store bytes, outer, framed scope results.length active [.label results.length [] body]⟩ dst) :
    (∃ mid, Internal ⟨mem.store bytes, active, body⟩ mid ∧ dst =
      ⟨mid.store, outer, framed scope results.length mid.frame [.label results.length [] mid.code]⟩) ∨
    ∃ out, PureStep active.module.types [.label results.length [] body] out ∧
      dst = ⟨mem.store bytes, outer, framed scope results.length active out⟩ := by
  cases scope with
  | none => exact Computed.lime_body_step_cases move
  | some context =>
    change Step CallFrame.limeNoHost _ _ at move
    have native : Step CallFrame.limeNoHost ⟨mem.store bytes, outer,
        [.frame context.arity active [.label context.arity [] (values context.saved ++
          .label results.length [] body :: context.tail)]]⟩ dst := by
      simpa only [framed_some, List.append_assoc, List.singleton_append] using move
    have outerBody := Computed.lime_body_step_cases native
    rcases outerBody with ⟨mid, inside, rfl⟩ | ⟨out, pop, _⟩
    · have inner := Blocks.Context.lime_label_cont_iff (s := mem.store bytes) (f := active) (dst := mid) (saved := context.saved)
        (rest := context.tail) (n := results.length) (cont := []) (body := body)
      rcases inner.mp inside with ⟨next, step, rfl⟩ | ⟨out, pop, rfl⟩
      · exact .inl ⟨next, step, by simp only [framed_some, List.append_assoc, List.singleton_append]⟩
      · exact .inr ⟨out, pop, rfl⟩
    · exact (Computed.lime_label_stays (stack := context.saved) rfl (by simp) (by simp) (by simp) pop).elim

private theorem underLabel {body : List Admin}
    (stays : ∀ out, ¬ PureStep active.module.types [.label results.length [] body] out)
    (move : Internal ⟨mem.store bytes, outer, framed scope results.length active [.label results.length [] body]⟩ dst) :
    ∃ mid, Internal ⟨mem.store bytes, active, body⟩ mid ∧ dst =
      ⟨mid.store, outer, framed scope results.length mid.frame [.label results.length [] mid.code]⟩ := by
  rcases body_cases move with inside | ⟨out, exiting, _⟩
  · exact inside
  · exact (stays out exiting).elim

private theorem closeLabel {r : Result}
    (move : Internal ⟨mem.store bytes, outer, framed scope results.length active [.label results.length [] (result r)]⟩ dst) :
    dst = ⟨mem.store bytes, outer, framed scope results.length active (result r)⟩ := by
  cases r with
  | values vs =>
    rcases body_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .values vs) inside).elim
    · rw [Nested.lime_label_result (r := .values vs) pop]
      rfl
  | trap =>
    rcases body_cases move with ⟨_, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · rw [Nested.lime_label_result (r := .trap) pop]
      rfl

private theorem located {site : Site H} {args saved : List Value} {ops : List (Op H)}
    (allocated : site.Allocated base) (typed : site.Arguments args) :
    CalloutAt (renderIn mem outer active scope results.length ⟨bytes, .invoke saved site args ops⟩)
      (site.callout (invokeContextIn scope results.length active saved ops) args) :=
  ⟨rfl, allocated, by simpa [Site.callout] using congrArg List.length typed⟩

private theorem invoke_read {saved args : List Value} {site : Site H} {ops : List (Op H)}
    (ready : Ready mem host active results (.invoke saved site args ops)) (live : mem.Live bytes)
    (move : Step host (renderIn mem outer active scope results.length ⟨bytes, .invoke saved site args ops⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .invoke saved site args ops⟩ next ∧
      dst = renderIn mem outer active scope results.length next := by
  obtain ⟨allocated, typed, contract, _, _⟩ := ready
  have exactStep := Site.step_iff (dst := dst) (outer := outer)
    (context := invokeContextIn scope results.length active saved ops) allocated contract live typed
  rcases exactStep.mp move with ⟨next, out, nLive, nTyped, answer, rfl⟩ | ⟨diverges, rfl⟩
  · cases out with
    | values vs => exact ⟨⟨next, .source (saved ++ vs) ops⟩, .returned nLive nTyped answer,
        by simp [renderIn, Phase.renderIn, plug_invoke, result, List.append_assoc]⟩
        | trap => exact ⟨⟨next, .trapped saved (code ops)⟩, .trapped nLive answer,
        by simp [renderIn, Phase.renderIn, plug_invoke, result]⟩
  · exact ⟨_, .diverged diverges, rfl⟩

private theorem source_read {stack : List Value} {ops : List (Op H)}
    (ready : Ready mem host active results (.source stack ops))
    (move : Internal (renderIn mem outer active scope results.length ⟨bytes, .source stack ops⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .source stack ops⟩ next ∧
      dst = renderIn mem outer active scope results.length next := by
  cases ops with
  | nil =>
    have move' : Internal ⟨mem.store bytes, outer, framed scope results.length active [.label results.length [] (result (.values stack))]⟩ dst := by
      simpa [renderIn, Phase.renderIn, code, expression, result] using move
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
        by simp [renderIn, Phase.renderIn, List.append_assoc, values]⟩
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
        by simp [renderIn, Phase.renderIn, plug_invoke, List.append_assoc]⟩

private theorem trap_read {stack : List Value} {rest : List Admin}
    (move : Internal (renderIn mem outer active scope results.length ⟨bytes, .trapped stack rest⟩) dst) :
    ∃ next, Edge mem host active ⟨bytes, .trapped stack rest⟩ next ∧
      dst = renderIn mem outer active scope results.length next := by
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
    (move : Internal (renderIn mem outer active none results.length ⟨bytes, .frameResult r⟩) dst) :
    dst = renderIn mem outer active none results.length ⟨bytes, .done r⟩ := by
  cases r with
  | values vs => exact Nested.lime_frame_result (r := .values vs) move
  | trap => exact Nested.lime_frame_result (r := .trap) move

private theorem read {a : State H} (admittedScope : scope = none ∨ a.phase.InLabel) (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes)
    (move : Step host (renderIn mem outer active scope results.length a) dst) :
    ∃ next, Edge mem host active a next ∧ dst = renderIn mem outer active scope results.length next := by
  rcases a with ⟨bytes, phase⟩
  cases phase with
  | source stack ops =>
    have absent : decompose? (renderIn mem outer active scope results.length ⟨bytes, .source stack ops⟩) = none := by
      cases ops with
      | nil => cases scope <;> simp [decompose?, renderIn, Phase.renderIn, code, expression, List.append_assoc]
      | cons op ops => cases scope <;> cases op <;> simp [decompose?, renderIn, Phase.renderIn, code, Op.instr, expression, asValue?, List.append_assoc]
    exact source_read ready ((withoutCallout absent).mp move)
  | invoke saved site args ops => exact invoke_read ready live move
  | trapped stack rest =>
    have absent : decompose? (renderIn mem outer active scope results.length ⟨bytes, .trapped stack rest⟩) = none := by
      cases scope <;> simp [decompose?, renderIn, Phase.renderIn, List.append_assoc]
    exact trap_read ((withoutCallout absent).mp move)
  | frameResult out =>
    rcases admittedScope with rfl | impossible
    swap
    · exact impossible.elim
    have absent : decompose? (renderIn mem outer active none results.length ⟨bytes, .frameResult out⟩) = none := by
      cases out <;> simp [decompose?, renderIn, Phase.renderIn, result]
    exact ⟨⟨bytes, .done out⟩, .frameDone, frame_read ((withoutCallout absent).mp move)⟩
  | done out =>
    have absent : decompose? (renderIn mem outer active scope results.length ⟨bytes, .done out⟩) = none := by
      cases out <;> simp [decompose?, renderIn, Phase.renderIn, result]
    have internal := (withoutCallout absent).mp move
    cases out with
    | values vs => exact (Nested.lime_result_stuck (r := .values vs) internal).elim
    | trap => exact (Nested.lime_result_stuck (r := .trap) internal).elim

private theorem sound {a b : State H} (admittedScope : scope = none ∨ a.phase.InLabel) (ready : Ready mem host active results a.phase) (edge : Edge mem host active a b) :
    Step host (renderIn mem outer active scope results.length a) (renderIn mem outer active scope results.length b) := by
  cases edge with
  | @get bytes stack index v ops found =>
    have get := (Computed.lime_local_get_iff (s := mem.store bytes) (stack := stack) (rest := code ops) found).mpr rfl
    have move := framed_step (scope := scope) (results := results) (outer := outer) (.label get results.length [])
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [renderIn, Phase.renderIn, code, Op.instr, expression, values, List.append_assoc] using move
  | @drop bytes stack v ops =>
    have drop := (Computed.lime_drop_iff (s := mem.store bytes) (f := active) (stack := stack)
      (v := v) (rest := code ops)).mpr rfl
    exact Step.of_internal (framed_step (.label drop results.length []))
  | @resolve bytes saved args index site ops typed =>
    obtain ⟨_, _, resolved, _, _⟩ := checked_call ready.1
    have call := (Computed.lime_direct_call_iff (s := mem.store bytes) (stack := saved ++ args)
      (tail := code ops) resolved).mpr rfl
    have move := framed_step (scope := scope) (results := results) (outer := outer) (.label call results.length [])
    apply Step.of_internal
    change Step CallFrame.limeNoHost _ _
    simpa [renderIn, Phase.renderIn, plug_invoke, code, Op.instr, expression, List.append_assoc, values] using move
  | @returned bytes next saved site args ops vs _ _ answer =>
    have atHost := located (mem := mem) (scope := scope) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.1 ready.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, renderIn, Phase.renderIn, Site.callout,
      Execution.Runtime.Callout.fill, plug_invoke, result, List.append_assoc] using move
  | @trapped bytes next saved site args ops _ answer =>
    have atHost := located (mem := mem) (scope := scope) (results := results) (outer := outer) (active := active)
      (bytes := bytes) (saved := saved) (ops := ops) ready.1 ready.2.1
    have move := Step.callout_returned atHost answer
    simpa [resume, renderIn, Phase.renderIn, Site.callout, Execution.Runtime.Callout.fill, plug_invoke, result] using move
  | diverged answer => exact Step.callout_diverged (located (scope := scope) (results := results) ready.1 ready.2.1) answer
  | @erase bytes stack kept removed before cut rest split suffix activeTrap =>
    have move : Internal ⟨mem.store bytes, active, values stack ++ .trap :: before⟩
        ⟨mem.store bytes, active, values kept ++ .trap :: rest⟩ :=
      Computed.lime_trap_front_iff.mpr ⟨kept, removed, cut, rest, split, suffix, activeTrap, rfl⟩
    exact Step.of_internal (framed_step (.label move results.length []))
  | labelTrap => exact framed_step (.pure _ _ (.labelTrap results.length []))
  | @labelResult bytes stack =>
    have move := framed_step (scope := scope) (results := results) (outer := outer)
      (.pure (host := host) (mem.store bytes) active (.labelDone results.length [] stack))
    simpa [renderIn, Phase.renderIn, code, expression, result] using move
  | @frameDone _ out =>
    rcases admittedScope with rfl | impossible
    swap
    · exact impossible.elim
    cases out with
    | trap => exact .pure _ _ (.frameTrap _ active)
    | values vs =>
      exact .pure _ _ (.frameDone _ active vs (by simpa using congrArg List.length ready))

theorem step_iff {a : State H} (admittedScope : scope = none ∨ a.phase.InLabel) (ready : Ready mem host active results a.phase) (live : mem.Live a.bytes) :
    Step host (renderIn mem outer active scope results.length a) dst ↔
      ∃ next, Edge mem host active a next ∧ dst = renderIn mem outer active scope results.length next := by
  refine ⟨read admittedScope ready live, ?_⟩
  rintro ⟨_, edge, rfl⟩
  exact sound admittedScope ready edge

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Proofs
