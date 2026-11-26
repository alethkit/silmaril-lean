module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Memory.Callee.Preservation
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Memory.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Lime1Context.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs

open Execution.Runtime (Frame FuncInst Result Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall (CallTarget Declaration)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed

set_option backward.isDefEq.respectTransparency false

variable {H : Type} {base : Store H} {mem : Memory32 base} {callee : MemoryTarget} {site : IndirectSite}
  {caller : Frame} {saved : List Value} {tail : List Admin} {bytes : ByteArray} {dst : Config H}

local notation "resultCount" => callee.fn.declaration.results.length
local notation "cfg" => config mem caller saved tail callee

@[simp] private theorem code_nil : code [] = [] := rfl

@[simp] private theorem code_cons (op : Graph.Memory32.Op) (ops : List Graph.Memory32.Op) :
    code (op :: ops) = .source op.v1.toLime :: code ops := rfl

private theorem enter_iff {args : List Value} (allocated : callee.Allocated base)
    (typed : args.map Value.type = callee.fn.declaration.params) :
    Step CallFrame.limeNoHost (cfg bytes (.invoke args)) dst ↔ dst = cfg bytes (.body args callee.fn.initial callee.fn.code) := by
  have count : args.length = callee.fn.declaration.params.length := by simpa using congrArg List.length typed
  have exactInvoke {mid : Config H} :=
    CallFrame.lime_invoke_wasm_prefix_iff (s := mem.store bytes) (caller := caller)
      (saved := saved) (args := args) (dst := mid) allocated count
  have body : expression callee.code.body = values callee.fn.initial ++ code callee.fn.code := by
    have literal (v : Value) :
        (Execution.Runtime.AdminInstr.source (Graph.v1CodeSyntax.ops.value v).toLime : Admin) = value v := by
      rcases v with ⟨type, bits⟩
      cases type <;> rfl
    simp [MemoryTarget.code, Graph.Memory32.Function.v1Func, Wasm.V1.Func.toLime,
      Wasm.V1.Expr.toLime_eq_map, expression, values, code, List.map_map, Function.comp_def, literal]
  constructor
  · intro move
    obtain ⟨mid, invoked, rfl⟩ := CallContinuation.lime_invoke_strip_suffix
      (stack := saved ++ args) (rest := tail) (a := callee.address)
      (by simpa only [config, render, values_append, List.append_assoc, List.singleton_append] using move)
    obtain rfl := exactInvoke.mp invoked
    simp [config, render, Declaration.frame, Declaration.type, MemoryTarget.code, Graph.Memory32.Function.v1Func, Wasm.V1.Func.toLime, ← body]
  · rintro rfl
    have step := exactInvoke.mpr rfl
    have locals : callee.code.locals = callee.fn.declaration.locals := rfl
    rw [body, locals] at step
    simpa [config, render, values, List.append_assoc, Declaration.frame, Declaration.type] using
      Step.context step [] tail

private theorem body_iff {args : List Value} {body : List Admin}
    (stays : ∀ out, ¬ PureStep callee.fn.declaration.module.types [.label resultCount [] body] out) :
    Step CallFrame.limeNoHost ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args) saved tail body⟩ dst ↔
      ∃ mid, Step CallFrame.limeNoHost ⟨mem.store bytes, callee.fn.declaration.frame args, body⟩ mid ∧
        dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail mid.code⟩ := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv move
    rcases lime_body_step_cases step with ⟨next, inside, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨next, inside, by simp [MemoryWrite.limeActivationCode, List.append_assoc]⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, step, rfl⟩
    simpa only [MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
      Step.context (Step.frame (Step.label step resultCount []) resultCount caller) saved tail

private theorem leave_label_iff {args : List Value} {out : Result} :
    Step CallFrame.limeNoHost ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args) saved tail (result out)⟩ dst ↔
      dst = cfg bytes (.exit args out) := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv move
    rcases lime_body_step_cases step with ⟨_, inside, _⟩ | ⟨after, pop, rfl⟩
    · cases out with
      | values vs => exact (Nested.lime_result_stuck (r := .values vs) inside).elim
      | trap => exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · cases out with
      | values vs => rw [Nested.lime_label_result (r := .values vs) pop]; rfl
      | trap => rw [Nested.lime_label_result (r := .trap) pop]; rfl
  · rintro rfl
    cases out with
    | values vs =>
      simpa only [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelDone resultCount [] vs)) resultCount caller) saved tail
    | trap =>
      simpa only [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using
        Step.context (Step.frame (Step.pure (host := CallFrame.limeNoHost) (mem.store bytes)
          (callee.fn.declaration.frame args) (.labelTrap resultCount [])) resultCount caller) saved tail

private theorem leave_frame_iff {args : List Value} {out : Result} (typed : resultTyped callee out) :
    Step CallFrame.limeNoHost (cfg bytes (.exit args out)) dst ↔ dst = cfg bytes (.done out) := by
  constructor
  · intro move
    obtain ⟨mid, step, rfl⟩ := CallContinuation.lime_frame_context_inv
      (by simpa only [config, render, List.append_assoc, List.singleton_append] using move)
    cases out with
    | values vs => obtain rfl := Nested.lime_frame_result (r := .values vs) step; rfl
    | trap => obtain rfl := Nested.lime_frame_result (r := .trap) step; rfl
  · rintro rfl
    cases out with
    | values vs =>
      have count : vs.length = resultCount := by simpa using congrArg List.length typed
      exact Step.context (.pure _ _ (.frameDone resultCount (callee.fn.declaration.frame args) vs count)) saved tail
    | trap => exact Step.context (.pure _ _ (.frameTrap resultCount (callee.fn.declaration.frame args))) saved tail

private theorem get_iff {args stack : List Value} {index : LocalIdx} {ops : List Graph.Memory32.Op}
    {v : Value} (found : (callee.fn.declaration.frame args).locals[index.toNat]? = some v) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops))) dst ↔
      dst = cfg bytes (.body args (stack ++ [v]) ops) := by
  rw [show cfg bytes (.body args stack (.ranked (.numeric (.get index)) :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source (.localGet index) :: code ops)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain rfl := (lime_local_get_iff found).mp step
    simp [config, render, MemoryWrite.limeActivationCode, values, List.append_assoc]
  · rintro rfl
    exact ⟨_, (lime_local_get_iff found).mpr rfl, by
      simp [config, render, MemoryWrite.limeActivationCode, values, List.append_assoc]⟩

private theorem load_iff {args stack : List Value} {offset : Fin (2 ^ 32)} {ptr : BitVec 32}
    {ops : List Graph.Memory32.Op} (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 ptr]) (.load offset :: ops))) dst ↔
      (∃ bits, MemoryQuery.EdgeAt bytes offset.val (.load ptr) (.value bits) ∧
        dst = cfg bytes (.body args (stack ++ [Value.int .i32 bits]) ops)) ∨
      (MemoryQuery.EdgeAt bytes offset.val (.load ptr) .trap ∧ dst = cfg bytes (.trapped args stack (code ops))) := by
  let arg := Graph.Memory32.immediate offset
  have slot := mem.frameMemory_store (bytes := bytes) (active := callee.fn.declaration.frame args) checked.slot
  have access := MemoryWrite.lime_activation_load_step_iff_at
    (host := CallFrame.limeNoHost) (caller := caller) (arity := resultCount) (callerSaved := saved)
    (callerTail := tail) (saved := stack) (tail := code ops) (immediate := arg) (ptr := ptr) (dst := dst) slot
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 ptr]) (.load offset :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ MemoryQuery.limeCodeAt arg (.load ptr) ++ code ops)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
      values_append, List.append_assoc, List.singleton_append]
    rfl]
  rw [access]
  constructor
  · rintro ⟨out, edge, rfl⟩
    cases out with
    | value bits =>
      exact .inl ⟨bits, edge, by
        simp [config, render, values, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
          value, Value.int, List.append_assoc]⟩
    | trap =>
      exact .inr ⟨edge, by simp [config, render, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
        List.append_assoc]⟩
    | size | load => cases MemoryQuery.invert_at edge
  · rintro (⟨bits, edge, rfl⟩ | ⟨edge, rfl⟩)
    · exact ⟨.value bits, edge, by simp [config, render, MemoryWrite.limeActivationCode,
        MemoryQuery.limeCodeAt, values, value, Value.int, List.append_assoc]⟩
    · exact ⟨.trap, edge, by simp [config, render, MemoryWrite.limeActivationCode, MemoryQuery.limeCodeAt,
        List.append_assoc]⟩

private theorem store_iff {args stack : List Value} {offset : Fin (2 ^ 32)} {ptr word : BitVec 32}
    {ops : List Graph.Memory32.Op} (checked : callee.Checked mem) (live : mem.Live bytes) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 ptr, Value.int .i32 word]) (.store offset :: ops))) dst ↔
      (∃ written, MemoryWrite.EdgeAt bytes offset.val (.store ptr word) (.written written) ∧ mem.Live written ∧
        dst = cfg written (.body args stack ops)) ∨
      (MemoryWrite.EdgeAt bytes offset.val (.store ptr word) .trap ∧
        dst = cfg bytes (.trapped args stack (code ops))) := by
  let arg := Graph.Memory32.immediate offset
  have access := mem.activation_store_iff_at
    (bytes := bytes) (host := CallFrame.limeNoHost) (caller := caller) (callee := callee.fn.declaration.frame args)
    (arity := resultCount) (callerSaved := saved) (callerTail := tail) (saved := stack) (tail := code ops)
    (arg := arg) (ptr := ptr) (word := word) (dst := dst) checked.slot live
  simpa [config, render, Graph.Memory32.Op.v1, Wasm.V1.Instr.toLime, MemoryWrite.limeActivationCode,
    MemoryWrite.limeConfigAt, value, Value.int, values, List.append_assoc, arg, Graph.Memory32.immediate] using access

private theorem size_iff {args stack : List Value} {ops : List Graph.Memory32.Op}
    (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args stack (.size :: ops))) dst ↔
      dst = cfg bytes (.body args (stack ++ [pages bytes]) ops) := by
  rw [show cfg bytes (.body args stack (.size :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .source .memorySize :: code ops)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have slot := mem.frameMemory_store (bytes := bytes) (active := callee.fn.declaration.frame args) checked.slot
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨head, size, rfl⟩ := CallContinuation.lime_memorySize_strip step
    obtain ⟨out, edge, rfl⟩ := (MemoryQuery.lime_step_iff_at MemoryQuery.arg slot (query := .size)).mp size
    cases MemoryQuery.invert edge
    simp [config, render, MemoryWrite.limeActivationCode, MemoryQuery.limeConfigAt,
      MemoryQuery.limeCodeAt, pages, values, value, Value.int, List.append_assoc]
  · rintro rfl
    have size := MemoryQuery.lime_sound (host := CallFrame.limeNoHost) slot (MemoryQuery.fact .size)
    refine ⟨⟨mem.store bytes, callee.fn.declaration.frame args, values (stack ++ [pages bytes]) ++ code ops⟩,
      ?_, by simp only [config, render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
    simpa [MemoryQuery.limeConfigAt, MemoryQuery.limeCodeAt, pages, values, value, Value.int, List.append_assoc] using
      Step.context size stack (code ops)

private theorem grow_iff {args stack : List Value} {delta : BitVec 32} {ops : List Graph.Memory32.Op}
    (checked : callee.Checked mem) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 delta]) (.grow :: ops))) dst ↔
      (∃ grown, MemoryGrow.Edge (mem.current bytes) (.request delta) (.grown grown) ∧
        dst = cfg grown (.body args (stack ++ [pages bytes]) ops)) ∨
      dst = cfg bytes (.body args (stack ++ [Value.int .i32 (-1)]) ops) := by
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 delta]) (.grow :: ops)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ [Value.int .i32 delta]) ++ .source .memoryGrow :: code ops)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have slot : frameMemory (mem.store bytes) (callee.fn.declaration.frame args) =
      some (mem.address, mem.current bytes) := mem.frameMemory_store checked.slot
  have storeAgain (grown : ByteArray) :
      setMemory (mem.store bytes) mem.address (mem.current grown) = mem.store grown := by
    simp [Memory32.store, setMemory, List.set_set]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨head, grow, rfl⟩ := CallContinuation.lime_memoryGrow_strip step
    obtain ⟨out, edge, rfl⟩ := (MemoryGrow.lime_step_iff slot (q := .request delta)).mp grow
    cases out with
    | request => cases MemoryGrow.invert edge
    | grown grown =>
      refine .inl ⟨grown, edge, ?_⟩
      simp [config, render, MemoryWrite.limeActivationCode, MemoryGrow.limeConfig,
        Memory32.current, pages, values, value, Value.int, List.append_assoc]
      simpa only [Memory32.current] using storeAgain grown
    | failed =>
      exact .inr (by simp [config, render, MemoryWrite.limeActivationCode, MemoryGrow.limeConfig,
        values, value, Value.int, List.append_assoc])
  · rintro (⟨grown, edge, rfl⟩ | rfl)
    · have grow := MemoryGrow.lime_sound (host := CallFrame.limeNoHost) slot edge
      refine ⟨⟨mem.store grown, callee.fn.declaration.frame args, values (stack ++ [pages bytes]) ++ code ops⟩,
        ?_, by simp only [config, render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
      simpa [MemoryGrow.limeConfig, Memory32.current, pages, values, value, Value.int, List.append_assoc,
        show setMemory (mem.store bytes) mem.address { mem.initial with data := grown } = mem.store grown
          from storeAgain grown] using Step.context grow stack (code ops)
    · have grow := MemoryGrow.lime_sound (host := CallFrame.limeNoHost) slot (MemoryGrow.fact (.fail delta))
      refine ⟨⟨mem.store bytes, callee.fn.declaration.frame args,
        values (stack ++ [Value.int .i32 (-1)]) ++ code ops⟩, ?_,
        by simp only [config, render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]⟩
      simpa [MemoryGrow.limeConfig, values, value, Value.int, List.append_assoc] using
        Step.context grow stack (code ops)

private theorem erase_iff {args stack : List Value} {rest : List Admin} (active : stack ≠ [] ∨ rest ≠ []) :
    Step CallFrame.limeNoHost (cfg bytes (.trapped args stack rest)) dst ↔
      ∃ kept removed cut after, stack = kept ++ removed ∧ rest = cut ++ after ∧
        (removed ≠ [] ∨ cut ≠ []) ∧ dst = cfg bytes (.trapped args kept after) := by
  rw [show cfg bytes (.trapped args stack rest) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values stack ++ .trap :: rest)⟩ from by
    simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (fun _ => active))]
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩ := lime_trap_front_iff.mp step
    exact ⟨kept, removed, cut, after, split, suffix, nonempty,
      by simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]⟩
  · rintro ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩
    exact ⟨_, lime_trap_front_iff.mpr ⟨kept, removed, cut, after, split, suffix, nonempty, rfl⟩,
      by simp [config, render, MemoryWrite.limeActivationCode, List.append_assoc]⟩

theorem stays {phase : Phase} (notDone : ∀ out, phase ≠ .done out)
    {types : List Wasm.Lime1.FuncType} {n : Nat} {cont : Wasm.Lime1.Expr} {out : List Admin} :
    ¬ PureStep types [.label n cont (values saved ++ render callee phase ++ tail)] out := by
  have frameStays {k : Nat} {fr : Frame} {body : List Admin} :
      ¬ PureStep types [.label n cont (values saved ++ .frame k fr body :: tail)] out :=
    lime_label_stays rfl (by simp) (by simp) (by simp)
  cases phase with
  | invoke args =>
    simpa only [render, values_append, List.append_assoc, List.singleton_append] using
      (lime_label_stays (types := types) (n := n) (cont := cont) (out := out)
        (stack := saved ++ args) (head := .invoke callee.address) (rest := tail) rfl
        (by simp) (by simp) (by simp))
  | body | child | trapped | exit => simpa only [render, List.append_assoc, List.singleton_append] using frameStays
  | done out => exact (notDone out rfl).elim

private theorem call_iff {args stack operands : List Value} {target : CallTarget}
    {child : MemoryTarget} {rest : List Graph.Memory32.Op}
    (link : site.MemoryDirect (base := base) callee target child) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ operands) (.ranked (.call target) :: rest))) dst ↔
      dst = cfg bytes (.child args stack child (.invoke operands) rest) := by
  rw [show cfg bytes (.body args (stack ++ operands) (.ranked (.call target) :: rest)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ operands) ++ .source (.call target.index) :: code rest)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have resolve {mid : Config H} := lime_direct_call_iff (s := mem.store bytes)
    (f := callee.fn.declaration.frame args) (stack := stack ++ operands) (tail := code rest) (dst := mid) link.resolves
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain rfl := resolve.mp step
    simp [config, render, MemoryWrite.limeActivationCode, link.address, values_append, List.append_assoc]
  · rintro rfl
    exact ⟨_, resolve.mpr rfl, by
      simp [config, render, MemoryWrite.limeActivationCode, link.address, values_append, List.append_assoc]⟩

private theorem indirect_linked {index : TypeIdx} {signature : Wasm.V1.FuncType}
    (link : site.MemoryIndirect base callee index signature) :
    (site.memorySite index signature).Linked base callee.fn.declaration.module := by
  refine ⟨link.tableAt, link.signatureAt, rfl, ?_, ?_⟩
  · intro address fn found
    simp [IndirectSite.memorySite, Graph.Program.lookup] at found
  · intro address member
    obtain ⟨fn, allocated, registered⟩ := link.entries address member
    refine ⟨fn, allocated, fun typed => ?_⟩
    cases fn with
    | host => trivial
    | wasm =>
      obtain ⟨child, found, exactAllocation, _⟩ := registered typed
      exact .inr ⟨child, found, exactAllocation⟩

private theorem indirect_iff {args stack : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType}
    {selector : BitVec 32} {rest : List Graph.Memory32.Op}
    (link : site.MemoryIndirect base callee index signature) :
    Step CallFrame.limeNoHost (cfg bytes (.body args (stack ++ [Value.int .i32 selector])
      (.callIndirect index signature :: rest))) dst ↔
      ∃ target, (site.memorySite index signature).Lookup base selector target ∧
        dst = ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount
          (callee.fn.declaration.frame args) saved tail
          (values stack ++ IndirectSite.lookupHead target :: code rest)⟩ := by
  rw [show cfg bytes (.body args (stack ++ [Value.int .i32 selector]) (.callIndirect index signature :: rest)) =
      ⟨mem.store bytes, caller, MemoryWrite.limeActivationCode resultCount (callee.fn.declaration.frame args)
        saved tail (values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect index) :: code rest)⟩ from by
    simp only [config, render, code_cons, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
    rfl]
  rw [body_iff (fun _ => lime_label_stays rfl (by simp) (by simp) (by simp))]
  have resolve {mid : Config H} := IndirectSite.step_iff (memory := mem) (bytes := bytes)
    (indirect := site.memorySite index signature) (active := callee.fn.declaration.frame args)
    (stack := stack) (selector := selector) (rest := code rest) (dst := mid) (indirect_linked link)
  constructor
  · rintro ⟨mid, step, rfl⟩
    obtain ⟨target, lookup, rfl⟩ := resolve.mp step
    exact ⟨target, lookup, rfl⟩
  · rintro ⟨target, lookup, rfl⟩
    exact ⟨_, resolve.mpr ⟨target, lookup, rfl⟩, rfl⟩

private theorem indirect_target {index : TypeIdx} {signature : Wasm.V1.FuncType} {selector : BitVec 32}
    {target : IndirectTarget H} (link : site.MemoryIndirect base callee index signature)
    (lookup : (site.memorySite index signature).Lookup base selector (some target)) :
    ∃ child, target = .memory child ∧ child.fn.rank < callee.fn.rank := by
  cases lookup with
  | host entry allocated =>
    obtain ⟨fn, found, registered⟩ := link.entries _ (List.mem_of_getElem? entry)
    rw [allocated] at found
    cases found
    obtain ⟨_, _, wasmAllocation, _⟩ := registered rfl
    unfold MemoryTarget.Allocated Site.Allocated at *
    rw [allocated] at wasmAllocation
    cases wasmAllocation
  | wasm _ found _ _ =>
    simp [IndirectSite.memorySite, Graph.Program.lookup] at found
  | memory entry found allocated typed =>
    obtain ⟨fn, seen, registered⟩ := link.entries _ (List.mem_of_getElem? entry)
    unfold MemoryTarget.Allocated at allocated
    rw [allocated] at seen
    cases seen
    obtain ⟨other, same, _, smaller⟩ := registered typed
    change site.memoryLookup _ = _ at found
    rw [found] at same
    cases same
    exact ⟨_, rfl, smaller⟩

private theorem child_context {args stack : List Value} {child : MemoryTarget} {phase : Phase}
    {rest : List Graph.Memory32.Op} (notDone : ∀ out, phase ≠ .done out) :
    Step CallFrame.limeNoHost (cfg bytes (.child args stack child phase rest)) dst ↔
      ∃ mid,
        Step CallFrame.limeNoHost (config mem (callee.fn.declaration.frame args) stack (code rest) child bytes phase) mid ∧
        dst = ⟨mid.store, caller, MemoryWrite.limeActivationCode resultCount mid.frame saved tail mid.code⟩ := by
  have keep := body_iff (mem := mem) (callee := callee) (caller := caller) (saved := saved)
    (tail := tail) (bytes := bytes) (args := args) (dst := dst)
    (fun _ => stays (callee := child) (saved := stack) (tail := code rest) notDone)
  simpa only [config, render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append] using keep

private theorem read {phase : Phase} (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (ready : Ready mem site callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out)
    (move : Step CallFrame.limeNoHost (cfg bytes phase) dst) :
    ∃ nextBytes next, Edge mem site callee bytes phase nextBytes next ∧ dst = cfg nextBytes next := by
  induction phase generalizing callee caller saved tail bytes dst with
  | invoke args => exact ⟨_, _, .enter, (enter_iff allocated ready).mp move⟩
  | body args stack ops =>
    have checked := linked.checked callee registered
    cases ops with
    | nil =>
      have step := leave_label_iff (args := args) (out := .values stack)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst)
      exact ⟨_, _, .labelDone, step.mp (by simpa [config, render, MemoryWrite.limeActivationCode, result,
        List.append_assoc] using move)⟩
    | cons op ops =>
      have supported := List.all_eq_true.mp ready.2.1 op (List.mem_cons_self ..)
      cases op with
      | load offset =>
        obtain ⟨stack, ptr, rfl, _⟩ := Graph.Memory32.Function.load_typed ready.2.2.1
        rcases (load_iff checked).mp move with ⟨bits, edge, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .load edge, eq⟩
        · exact ⟨_, _, .loadTrap edge, eq⟩
      | store offset =>
        obtain ⟨stack, ptr, word, rfl, _⟩ := Graph.Memory32.Function.store_typed ready.2.2.1
        rcases (store_iff checked live).mp move with ⟨written, edge, _, eq⟩ | ⟨edge, eq⟩
        · exact ⟨_, _, .store edge, eq⟩
        · exact ⟨_, _, .storeTrap edge, eq⟩
      | size => exact ⟨_, _, .size, (size_iff checked).mp move⟩
      | grow =>
        obtain ⟨stack, delta, rfl, _⟩ := Graph.Memory32.Function.grow_typed ready.2.2.1
        rcases (grow_iff checked).mp move with ⟨grown, edge, eq⟩ | eq
        · exact ⟨_, _, .grow supported edge, eq⟩
        · exact ⟨_, _, .growFail, eq⟩
      | ranked op =>
        cases op with
        | numeric op =>
          cases op with
          | get index =>
            obtain ⟨v, found, _⟩ := get_typed ready.1 ready.2.2.1
            exact ⟨_, _, .get found, (get_iff found).mp move⟩
          | bin => contradiction
        | call target =>
          obtain ⟨stack, operands, rfl, typed, used, _⟩ := call_typed ready.2.2.1
          obtain ⟨child, link⟩ := linked.direct callee registered target used
          exact ⟨_, _, .call link typed, (call_iff link).mp move⟩
        | _ => contradiction
      | callIndirect index signature =>
        obtain ⟨stack, operands, selector, rfl, typed, _⟩ := indirect_typed ready.2.2.1
        have link := linked.indirect callee registered index signature (ready.2.2.2 _ (by simp))
        obtain ⟨target, lookup, rfl⟩ := (indirect_iff link).mp move
        cases target with
        | none =>
          refine ⟨_, _, .indirectTrap lookup, ?_⟩
          simp [config, render, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]
        | some target =>
          obtain ⟨child, rfl, smaller⟩ := indirect_target link lookup
          refine ⟨_, _, .callIndirect lookup smaller typed, ?_⟩
          simp [config, render, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, values_append, List.append_assoc]
      | _ => contradiction
  | child args stack child phase rest ih =>
    obtain ⟨_, found, childAllocated, _, childActive, childReady, _, _, _⟩ := ready
    obtain ⟨mid, inside, rfl⟩ := (child_context childActive).mp move
    obtain ⟨written, next, step, rfl⟩ := ih found childAllocated childReady live childActive inside
    refine ⟨_, _, .child step, ?_⟩
    simp only [config, after_child_render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
  | trapped args stack rest =>
    by_cases active : stack ≠ [] ∨ rest ≠ []
    · obtain ⟨kept, removed, cut, after, split, suffix, nonempty, eq⟩ := (erase_iff active).mp move
      exact ⟨_, _, .erase split suffix nonempty, eq⟩
    · obtain ⟨stackNil, restNil⟩ := not_or.mp active
      have : stack = [] := not_not.mp stackNil
      have : rest = [] := not_not.mp restNil
      subst stack rest
      have step := leave_label_iff (args := args) (out := .trap)
        (mem := mem) (callee := callee) (bytes := bytes) (caller := caller) (saved := saved) (tail := tail) (dst := dst)
      exact ⟨_, _, .labelTrap, step.mp (by simpa [config, render, MemoryWrite.limeActivationCode, result,
        values, List.append_assoc] using move)⟩
  | exit args out => exact ⟨_, _, .frameDone, (leave_frame_iff ready.2).mp move⟩
  | done out => exact (notDone out rfl).elim

private theorem sound {phase next : Phase} {written : ByteArray} (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn)
    (allocated : callee.Allocated base) (ready : Ready mem site callee phase) (live : mem.Live bytes)
    (move : Edge mem site callee bytes phase written next) : Step CallFrame.limeNoHost (cfg bytes phase) (cfg written next) := by
  induction move generalizing caller saved tail with
  | enter => exact (enter_iff allocated ready).mpr rfl
  | get found => exact (get_iff found).mpr rfl
  | load edge => exact (load_iff (linked.checked _ registered)).mpr (.inl ⟨_, edge, rfl⟩)
  | loadTrap edge => exact (load_iff (linked.checked _ registered)).mpr (.inr ⟨edge, rfl⟩)
  | store edge =>
    exact (store_iff (linked.checked _ registered) live).mpr
      (.inl ⟨_, edge, mem.live_same_size live (MemoryWrite.closed_at edge), rfl⟩)
  | storeTrap edge => exact (store_iff (linked.checked _ registered) live).mpr (.inr ⟨edge, rfl⟩)
  | size => exact (size_iff (linked.checked _ registered)).mpr rfl
  | grow _ edge => exact (grow_iff (linked.checked _ registered)).mpr (.inl ⟨_, edge, rfl⟩)
  | growFail => exact (grow_iff (linked.checked _ registered)).mpr (.inr rfl)
  | call link _ => exact (call_iff link).mpr rfl
  | @callIndirect callee child bytes args operandsSaved operands index signature selector rest lookup _ _ =>
    have link := linked.indirect callee registered index signature (ready.2.2.2 _ (by simp))
    refine (indirect_iff link).mpr ⟨_, lookup, ?_⟩
    simp [config, render, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, values_append, List.append_assoc]
  | @indirectTrap callee bytes args stack index signature selector rest lookup =>
    have link := linked.indirect callee registered index signature (ready.2.2.2 _ (by simp))
    refine (indirect_iff link).mpr ⟨none, lookup, ?_⟩
    simp [config, render, MemoryWrite.limeActivationCode, IndirectSite.lookupHead, List.append_assoc]
  | child move ih =>
    obtain ⟨_, found, childAllocated, _, childActive, childReady, _, _, _⟩ := ready
    refine (child_context childActive).mpr ⟨_, ih found childAllocated childReady live, ?_⟩
    simp only [config, after_child_render, MemoryWrite.limeActivationCode, List.append_assoc, List.singleton_append]
  | @erase callee bytes args stack kept removed before cut rest split suffix active =>
    have nonempty : stack ≠ [] ∨ before ≠ [] := by
      rcases active with removed | cut
      · exact .inl (fun h => removed ((List.append_eq_nil_iff.mp (split.symm.trans h)).2))
      · exact .inr (fun h => cut ((List.append_eq_nil_iff.mp (suffix.symm.trans h)).1))
    exact (erase_iff nonempty).mpr ⟨kept, _, _, rest, split, suffix, active, rfl⟩
  | @labelDone callee bytes args vs =>
    simpa [config, render, result, MemoryWrite.limeActivationCode, List.append_assoc] using
      (leave_label_iff (args := args) (out := .values vs) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail)).mpr rfl
  | @labelTrap callee bytes args =>
    simpa [config, render, result, MemoryWrite.limeActivationCode, values, List.append_assoc] using
      (leave_label_iff (args := args) (out := .trap) (bytes := bytes) (mem := mem) (caller := caller)
        (callee := callee) (saved := saved) (tail := tail)).mpr rfl
  | frameDone => exact (leave_frame_iff ready.2).mpr rfl

theorem step_iff {phase : Phase} (linked : site.MemoryLinked mem)
    (registered : site.memoryLookup callee.address = some callee.fn) (allocated : callee.Allocated base)
    (ready : Ready mem site callee phase) (live : mem.Live bytes) (notDone : ∀ out, phase ≠ .done out) :
    Step CallFrame.limeNoHost (cfg bytes phase) dst ↔
      ∃ written next, Edge mem site callee bytes phase written next ∧ dst = cfg written next :=
  ⟨read linked registered allocated ready live notDone, fun ⟨_, _, edge, eq⟩ =>
    eq.symm ▸ sound linked registered allocated ready live edge⟩

private theorem code_absent (s : Store H) (ops : List Graph.Memory32.Op) (stack : List Value) :
    Execution.Runtime.decomposeFrom? coding s stack (code ops) = none := by
  induction ops generalizing stack with
  | nil => rfl
  | cons op rest ih =>
    change Execution.Runtime.decomposeFrom? coding s stack (.source op.v1.toLime :: code rest) = none
    rw [decomposeFrom?_source_cons]
    cases asValue? (.source op.v1.toLime) <;> simp [ih]

theorem absent {phase : Phase} (allocated : callee.Allocated base)
    (ready : Ready mem site callee phase) (notDone : ∀ out, phase ≠ .done out) :
    Execution.Runtime.decomposeFrom? coding (mem.store bytes) [] (values saved ++ render callee phase ++ tail) = none := by
  induction phase generalizing callee saved tail with
  | invoke =>
    have liveAllocation : callee.Allocated (mem.store bytes) := allocated
    unfold MemoryTarget.Allocated at liveAllocation
    simp [render, List.append_assoc, decomposeFrom?_invoke_cons, Execution.Runtime.decomposeHead?, liveAllocation]
  | body _ _ ops => simp [render, List.append_assoc, code_absent]
  | child args stack child phase ops ih =>
    obtain ⟨_, _, childAllocated, _, childActive, childReady, _, _, _⟩ := ready
    have none := ih (callee := child) (saved := stack) (tail := code ops) childAllocated childReady childActive
    simp only [List.append_assoc, decomposeFrom?_values_append, List.nil_append] at none
    simp [render, none]
  | trapped => simp [render]
  | exit _ out => cases out <;> simp [render, result]
  | done out => exact (notDone out rfl).elim

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.MemoryCallee.Proofs
