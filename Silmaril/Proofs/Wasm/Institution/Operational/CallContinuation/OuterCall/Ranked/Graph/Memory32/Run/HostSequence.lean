module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Sequence.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Host.Body.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.V1.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.HostEntry
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Guard

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs

open Execution.Runtime (EvalCtx Frame MemAddr MemInst Value)
open Computed
open Wasm.V1.Execution
open HostEntry.Proofs (invoke_exact literal_expression numeric_expression framed_numeric_step framed_direct_step
  framed_trapped_step bytes_unique)

private theorem encode_expression {H : Type} (seq : Sequence H) (rest : List (HostSegment H)) :
    expression (encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) rest) = seq.continuation rest := by
  induction rest with
  | nil => rfl
  | cons segment rest ih =>
    change expression (segment.operands.map (Prefix.emit Graph.v1CodeSyntax.ops) ++
      .call segment.site.index :: encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) rest) = _
    rw [expression_append, numeric_expression]
    exact congrArg (fun tail => segment.operands.map (Prefix.emit v1Syntax) ++ .source (.call segment.site.index) :: tail) ih

private theorem entry_body {H : Type} (seq : Sequence H) :
    expression seq.v1Func.body = values seq.root.function.initial ++ seq.continuation (seq.first :: seq.later) := by
  change expression (seq.root.function.initial.map Graph.v1CodeSyntax.ops.value ++
    encode Graph.v1CodeSyntax.ops (v1Code seq.root.function.code) (seq.first :: seq.later)) = _
  rw [expression_append, literal_expression, encode_expression]

section Execution

variable {H : Type} {seq : Sequence H} {host : HostSemantics H} {mode : MemoryMode}
  {program : Program} {memory : MemAddr} {calls : CallMode} {base : Store H} {initial : MemInst}
  {start : ByteArray} {outer : Frame} {args : List Value}

local notation "live" => storeWithBytes base memory initial
local notation "renderPhase" => seq.render base memory initial start outer args
local notation "active" => seq.root.function.declaration.frame args
local notation "arity" => seq.root.function.declaration.results.length
local notation "rootFn" => seq.root.function

private theorem enter_step {dst : Config H} (checked : seq.Checked mode program memory calls base outer args) :
    Step host (renderPhase .invoke) dst ↔
      dst = renderPhase (.computing start (rootFn).initial seq.root.operands seq.root.site seq.later) := by
  have count : args.length = (rootFn).declaration.params.length := by simpa using congrArg List.length checked.parameters
  have allocated : (live start).funcs[seq.root.address.value]? =
      some (.wasm (rootFn).declaration.type (rootFn).declaration.module seq.v1Func) := checked.allocated
  have locals : seq.v1Func.locals = (rootFn).declaration.locals := rfl
  simpa only [render, entry_body, context, EvalCtx.plug, locals, Declaration.frame, continuation, encode, first, v1Syntax,
    List.append_assoc, Function.comp_apply] using
    (invoke_exact (host := host) (outer := outer) (dst := dst) allocated count checked.scalar)

private theorem root_call {dst : Config H} (checked : seq.Checked mode program memory calls base outer args) :
    Step host (renderPhase .call) dst ↔ dst = renderPhase .invoke :=
  HostCall.V1.direct_step_iff (tail := []) checked.resolved

private theorem numeric_step {bytes : ByteArray} {stack : List Value} {op : Prefix.Op} {rest : List Prefix.Op}
    {site : HostCall.V1.Site H} {later : List (HostSegment H)} {dst : Config H} :
    Step host (renderPhase (.computing bytes stack (op :: rest) site later)) dst ↔
      (∃ next, Prefix.Reduce (active).locals stack op (.values next) ∧
        dst = renderPhase (.computing bytes next rest site later)) ∨
      (∃ saved, Prefix.Reduce (active).locals stack op (.trap saved) ∧
        dst = renderPhase (.trapped bytes saved (rest.map (Prefix.emit v1Syntax) ++
          .source (.call site.index) :: seq.continuation later))) := by
  simp only [render, HostEntry.context, EvalCtx.plug, List.map_cons, List.append_assoc, List.cons_append]
  exact framed_numeric_step

private theorem host_call {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {dst : Config H}
    (linked : Linked site (rootFn).declaration.module base) :
    Step host (renderPhase (.computing bytes (saved ++ actual) [] site later)) dst ↔
      dst = renderPhase (.pending bytes saved actual site later) := by
  simpa only [render, HostEntry.context, EvalCtx.plug, List.map_nil, List.append_nil] using
    (framed_direct_step (f := active) (n := arity) (s := live bytes) (outer := outer)
      (stack := saved ++ actual) (tail := seq.continuation later) (host := host) (dst := dst) linked.resolved)

private theorem trap_step {bytes : ByteArray} {saved : List Value} {tail : List Admin} {dst : Config H} :
    Step host (renderPhase (.trapped bytes saved tail)) dst ↔
      (∃ kept rest, Prefix.Discard saved tail kept rest ∧ dst = renderPhase (.trapped bytes kept rest)) ∨
      (saved = [] ∧ tail = [] ∧ dst = renderPhase (.graph ⟨bytes, outer, [.frame arity active [.trap]]⟩)) :=
  framed_trapped_step

private theorem render_delivered {bytes : ByteArray} {saved : List Value} {later : List (HostSegment H)}
    (r : Execution.Runtime.Result) :
    renderPhase (seq.delivered outer args bytes saved later r) =
      ⟨live bytes, outer, (seq.root.context args).plug value (values saved ++ result r ++ seq.continuation later)⟩ := by
  cases r with
  | trap => simp [delivered, render, result, List.append_assoc]
  | values vs =>
    cases later <;> simp [delivered, resume, render, Memory32.render, continuation, encode, v1Syntax, result, List.append_assoc]

private theorem pending_step {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {dst : Config H} (linked : Linked site (rootFn).declaration.module base)
    (typed : actual.map Value.type = site.signature.params) :
    Step host (renderPhase (.pending bytes saved actual site later)) dst ↔
      (∃ s' r, host site.target (live bytes) actual (.returned s' r) ∧
        dst = ⟨s', outer, (seq.root.context args).plug value (values saved ++ result r ++ seq.continuation later)⟩) ∨
      (host site.target (live bytes) actual .diverged ∧ dst = renderPhase (.pending bytes saved actual site later)) := by
  have checked : site.Checked (live bytes) active actual := ⟨linked.resolved, linked.allocated, typed, linked.scalar⟩
  exact v1_host_pending_step_iff (k := seq.root.context args) (outer := outer)
    (saved := saved) (tail := seq.continuation later) checked

private theorem wrap_checked (checked : seq.Checked mode program memory calls base outer args)
    {code : List Admin} (guard : CodeAllowedFor mode program memory calls (rootFn).rank (active).module code) :
    CodeAllowedFor mode program memory calls ((rootFn).rank + 1) outer.module ((seq.root.context args).plug value code) := by
  have rank : calls.permits ((rootFn).rank + 1) (rootFn).rank := by cases calls <;> simp [CallMode.permits]
  exact RunProofs.single_allowed.mpr
    (.enteredFrame checked.scalar rank (RunProofs.single_allowed.mpr (.label checked.scalar guard)))

private theorem resume_ready (checked : seq.Checked mode program memory calls base outer args)
    {bytes : ByteArray} {stack : List Value} {later : List (HostSegment H)}
    (extent : mode.extent initial.data.size bytes) (listed : ∀ piece ∈ later, piece.site ∈ seq.sites)
    (typed : check rootFn (Prefix.stackTypes stack) later = true) :
    seq.Ready mode program memory calls initial (seq.resume outer args bytes stack later) := by
  cases later with
  | nil =>
    have tail : CodeAllowedFor mode program memory calls (rootFn).rank (active).module seq.root.tail := by
      apply RunProofs.tail_allowed (fn := rootFn) ?_ checked.slot checked.supportedTail
      intro target used
      obtain ⟨callee, found, _, linked, permitted⟩ := checked.linkedTail target used
      exact ⟨callee, found, linked, permitted⟩
    exact ⟨extent, wrap_checked checked (RunProofs.append_allowed.mpr ⟨RunProofs.values_allowed stack, tail⟩)⟩
  | cons piece rest =>
    exact ⟨extent, listed piece (.head _), fun later used => listed later (.tail _ used), typed⟩

theorem return_ready (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (contract : seq.Contract host mode memory initial base)
    {bytes : ByteArray} {saved actual : List Value} {site : HostCall.V1.Site H}
    {later : List (HostSegment H)} {after : Store H} {r : Execution.Runtime.Result}
    (ready : seq.Ready mode program memory calls initial (.pending bytes saved actual site later))
    (returned : host site.target (live bytes) actual (.returned after r)) :
    ∃ next, after = live next ∧ bytes.size ≤ next.size ∧ HostCall.V1.ResultTyped site.signature.results r ∧
      Layout program after memory { initial with data := next } ∧
      seq.Ready mode program memory calls initial (seq.delivered outer args next saved later r) := by
  obtain ⟨extent, listed, laterListed, typedArgs, continuation⟩ := ready
  obtain ⟨typed, storeEffect⟩ := contract site listed bytes extent actual typedArgs after r returned
  obtain ⟨next, stored, newExtent, mono, allocation⟩ := layout.host_store extent storeEffect
  refine ⟨next, stored, mono, typed, allocation, ?_⟩
  cases r with
  | trap => exact newExtent
  | values payload =>
    apply resume_ready checked newExtent laterListed
    have payloadTyped : payload.map Value.type = site.signature.results := typed
    simpa [Prefix.stackTypes, payloadTyped] using continuation

theorem preserves (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (extent : mode.extent initial.data.size start)
    (contract : seq.Contract host mode memory initial base) {src dst : Phase H}
    (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src) :
    seq.Ready mode program memory calls initial dst := by
  cases edge with
  | resolve => trivial
  | enter =>
    exact ⟨extent, .head _, fun piece used => .tail _ (List.mem_map.mpr ⟨piece, used, rfl⟩), checked.typedBody⟩
  | numeric moved =>
    obtain ⟨extent, listed, later, check⟩ := ready
    have locals : (active).locals.map Value.type = (rootFn).declaration.params ++ (rootFn).declaration.locals := by
      simp [Declaration.frame, checked.parameters, Value.zero, List.map_map, Function.comp_def]
    refine ⟨extent, listed, later, ?_⟩
    rw [← locals]
    exact check_prefix_preserves (locals.symm ▸ check) moved
  | prefixTrap _ => exact ready.1
  | discard _ => exact ready
  | closeTrap =>
    have rank : calls.permits ((rootFn).rank + 1) (rootFn).rank := by cases calls <;> simp [CallMode.permits]
    exact ⟨ready, RunProofs.single_allowed.mpr
      (.enteredFrame checked.scalar rank (RunProofs.single_allowed.mpr .trap))⟩
  | hostResolve typed =>
    obtain ⟨extent, listed, later, check⟩ := ready
    exact ⟨extent, listed, later, typed, check_prefix_resume check typed⟩
  | returned behavior stored =>
    obtain ⟨next, discovered, _, _, _, readyNext⟩ := return_ready checked layout contract ready behavior
    exact (bytes_unique layout (discovered.symm.trans stored)) ▸ readyNext
  | diverged _ => exact ready
  | graph moved => exact moved.ready graphChecked ready

private theorem sound (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    {src dst : Phase H} (edge : seq.Edge host mode program memory base initial start outer args src dst)
    (ready : seq.Ready mode program memory calls initial src) :
    Step host (renderPhase src) (renderPhase dst) := by
  cases edge with
  | resolve => exact (root_call checked).mpr rfl
  | enter => exact (enter_step checked).mpr rfl
  | numeric moved => exact numeric_step.mpr (.inl ⟨_, moved, rfl⟩)
  | prefixTrap moved => exact numeric_step.mpr (.inr ⟨_, moved, rfl⟩)
  | discard moved => exact trap_step.mpr (.inl ⟨_, _, moved, rfl⟩)
  | closeTrap => exact trap_step.mpr (.inr ⟨rfl, rfl, rfl⟩)
  | hostResolve _ => exact (host_call (checked.linkedHosts _ ready.2.1)).mpr rfl
  | returned behavior stored =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr
      (.inl ⟨_, _, behavior, (render_delivered _).trans (by cases stored; rfl)⟩)
  | diverged behavior =>
    obtain ⟨_, listed, _, arguments, _⟩ := ready
    exact (pending_step (checked.linkedHosts _ listed) arguments).mpr (.inr ⟨behavior, rfl⟩)
  | graph moved =>
    exact Step.of_internal ((v1_step_iff_at graphChecked layout matched ready).mpr
      ⟨_, moved, moved.ready graphChecked ready, rfl⟩)

private theorem readback (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src) {dst : Config H}
    (step : Step host (renderPhase src) dst) :
    ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧ dst = renderPhase next := by
  cases src with
  | call => exact ⟨_, .resolve, (root_call checked).mp step⟩
  | invoke => exact ⟨_, .enter, (enter_step checked).mp step⟩
  | computing bytes stack remaining site later =>
    cases remaining with
    | nil =>
      obtain ⟨saved, actual, rfl, typed, _⟩ := check_prefix_arguments ready.2.2.2
      exact ⟨_, .hostResolve typed, (host_call (checked.linkedHosts _ ready.2.1)).mp step⟩
    | cons op rest =>
      rcases numeric_step.mp step with ⟨next, moved, eq⟩ | ⟨saved, trapped, eq⟩
      · exact ⟨_, .numeric moved, eq⟩
      · exact ⟨_, .prefixTrap trapped, eq⟩
  | trapped bytes saved tail =>
    rcases trap_step.mp step with ⟨kept, rest, discarded, eq⟩ | ⟨rfl, rfl, eq⟩
    · exact ⟨_, .discard discarded, eq⟩
    · exact ⟨_, .closeTrap, eq⟩
  | pending bytes saved actual site later =>
    have ⟨_, listed, _, arguments, _⟩ := ready
    rcases (pending_step (checked.linkedHosts site listed) arguments).mp step with
      ⟨after, r, returned, eq⟩ | ⟨diverged, eq⟩
    · obtain ⟨next, stored, _, _, _, _⟩ := return_ready checked layout contract ready returned
      refine ⟨_, .returned returned stored, ?_⟩
      rw [render_delivered]
      rw [stored] at eq
      exact eq
    · exact ⟨_, .diverged diverged, eq⟩
  | graph state =>
    have internal := (ReadyFor.internal_iff layout ready).mp step
    obtain ⟨next, moved, _, eq⟩ := (v1_step_iff_at graphChecked layout matched ready).mp internal
    exact ⟨.graph next, .graph moved, eq⟩

theorem step_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src) {dst : Config H} :
    Step host (renderPhase src) dst ↔
      ∃ next, seq.Edge host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next ∧ dst = renderPhase next := by
  constructor
  · intro step
    obtain ⟨next, moved, eq⟩ := readback graphChecked checked layout matched contract ready step
    exact ⟨next, moved, preserves graphChecked checked layout extent contract moved ready, eq⟩
  · rintro ⟨next, moved, _, rfl⟩
    exact sound graphChecked checked layout matched moved ready

theorem trapped_run {bytes : ByteArray} {saved : List Value} {tail : List Admin} {dst : Phase H}
    (run : seq.Runs host mode program memory base initial start outer args (.trapped bytes saved tail) dst) :
    (∃ saved rest, dst = .trapped bytes saved rest) ∨ ∃ state, dst = .graph state := by
  induction run with
  | refl => exact .inl ⟨saved, tail, rfl⟩
  | tail _ transition ih =>
    rcases ih with ⟨saved, rest, rfl⟩ | ⟨state, rfl⟩
    · cases transition with
      | discard _ => exact .inl ⟨_, _, rfl⟩
      | closeTrap => exact .inr ⟨_, rfl⟩
    · cases transition with
      | graph _ => exact .inr ⟨_, rfl⟩

theorem run_iff (graphChecked : program.checkV1 memory mode calls = true)
    (checked : seq.Checked mode program memory calls base outer args)
    (layout : Layout program base memory initial) (matched : mode.matches initial)
    (extent : mode.extent initial.data.size start) (contract : seq.Contract host mode memory initial base)
    {src : Phase H} (ready : seq.Ready mode program memory calls initial src) {dst : Config H} :
    Steps host (renderPhase src) dst ↔
      ∃ next, seq.Runs host mode program memory base initial start outer args src next ∧
        seq.Ready mode program memory calls initial next ∧ dst = renderPhase next :=
  HostEntry.Proofs.finite_run_iff renderPhase _ _
    (fun {_ _} h => step_iff graphChecked checked layout matched extent contract h)
    (fun step h => preserves graphChecked checked layout extent contract step h) ready

end Execution
end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.HostEntry.Sequence.Proofs
