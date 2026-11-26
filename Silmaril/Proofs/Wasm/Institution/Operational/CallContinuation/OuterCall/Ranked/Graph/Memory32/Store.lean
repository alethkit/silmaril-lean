module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Typing
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.V1.Execution.Inversion
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Proofs

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution

theorem initial_shared {H : Type} {program : Program} {base : Store H} {a : MemAddr} {initial : MemInst}
    (layout : Layout program base a initial) : SharedStore base a initial base := by
  obtain ⟨inBounds, present⟩ := List.getElem?_eq_some_iff.mp layout.memory
  refine ⟨initial.data, rfl, ?_⟩
  change base = setMemory base a initial
  unfold setMemory
  rw [← present, List.set_getElem_self]

theorem frame_memory {H : Type} {program : Program} {base : Store H} {a : MemAddr} {initial : MemInst}
    (checked : program.checkV1 a = true) (layout : Layout program base a initial)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (locals : List Value) (bytes : ByteArray) :
    frameMemory (storeWithBytes base a initial bytes) (Graph.currentFrame fn.declaration locals) =
      some (a, { initial with data := bytes }) := by
  have slot := (function_checked checked found).2.2.2
  have before : frameMemory base (Graph.currentFrame fn.declaration locals) = some (a, initial) := by
    simp [frameMemory, Graph.currentFrame, slot, layout.memory]
  exact MemoryWrite.v1_frameMemory_setBytes before bytes

theorem update_shared {H : Type} {base : Store H} {a : MemAddr} {initial : MemInst}
    {bytes written : ByteArray} {offset : Nat} {address word : BitVec 32}
    (extent : bytes.size = initial.data.size)
    (edge : MemoryWrite.EdgeAt bytes offset (.store address word) (.written written)) :
    SharedStore base a initial (setMemory (storeWithBytes base a initial bytes) a
      { initial with data := written }) := by
  refine ⟨written, (MemoryWrite.closed_at edge).trans extent, ?_⟩
  simp [storeWithBytes, setMemory, List.set_set]

theorem function_allocated {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} (layout : Layout program base a initial)
    (shared : SharedStore base a initial live)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    live.funcs[address.value]? = some (.wasm fn.declaration.type fn.declaration.module fn.v1Func) := by
  obtain ⟨_, _, rfl⟩ := shared
  exact layout.functions address fn found

theorem body_expression (fn : Function) :
    expression fn.v1Func.body = values fn.initial ++ fn.code.map (.source ∘ Op.v1) := by
  change (fn.initial.map Graph.v1CodeSyntax.ops.value ++ fn.code.map Op.v1).map
    Execution.Runtime.AdminInstr.source = _
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  rcases v with ⟨t, bits⟩
  cases t <;> rfl

theorem enter {H : Type} {program : Program} {base live : Store H} {a : MemAddr} {initial : MemInst}
    (checked : program.checkV1 a = true) (layout : Layout program base a initial)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    (shared : SharedStore base a initial live) {caller : Frame} {saved args : List Value} {tail : List Admin}
    (typed : args.map Value.type = fn.declaration.params) :
    Step CallFrame.v1NoHost ⟨live, caller, values (saved ++ args) ++ .invoke address :: tail⟩
      ⟨live, caller, MemoryWrite.v1ActivationCode fn.declaration.results.head? (fn.declaration.frame args)
        saved tail (expression fn.v1Func.body)⟩ := by
  have count : args.length = fn.declaration.type.params.length := by
    simpa [Declaration.type] using congrArg List.length typed
  have arity := (function_checked checked found).1
  have scalar : fn.declaration.results.head?.toList.length = fn.declaration.results.length := by
    rw [← List.take_one, List.take_of_length_le arity]
  have start := Step.invokeWasm (host := CallFrame.v1NoHost) live
    caller address fn.declaration.type fn.declaration.module fn.v1Func args
    (function_allocated layout shared found) count arity
  simpa only [values_append, List.append_assoc, List.singleton_append, MemoryWrite.v1ActivationCode,
    scalar, Declaration.type, Declaration.frame, Function.v1Func] using Step.context start saved tail

theorem store_activation_shared {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} (checked : program.checkV1 a = true)
    (layout : Layout program base a initial) {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) (shared : SharedStore base a initial live)
    {caller : Frame} {locals callerSaved saved : List Value} {callerTail tail : List Admin}
    {offset : Fin (2 ^ 32)} {ptr word : BitVec 32} {dst : Config H}
    (move : Step CallFrame.v1NoHost ⟨live, caller,
      MemoryWrite.v1ActivationCode fn.declaration.results.head? (Graph.currentFrame fn.declaration locals)
        callerSaved callerTail (values saved ++ [.source (.intConst .i32 ptr),
          .source (.intConst .i32 word), .source ((Op.store offset).v1)] ++ tail)⟩ dst) :
    SharedStore base a initial dst.store ∧ dst.frame = caller := by
  obtain ⟨bytes, extent, rfl⟩ := shared
  obtain ⟨out, edge, eq⟩ := (MemoryWrite.v1_activation_store_step_iff_at
    (immediate := immediate offset) (address := ptr) (word := word) (saved := saved) (tail := tail)
    (frame_memory checked layout found locals bytes)).mp move
  rw [eq]
  cases MemoryWrite.invert_at edge with
  | write => exact ⟨update_shared extent edge, rfl⟩
  | trap => exact ⟨⟨bytes, extent, rfl⟩, rfl⟩

theorem load_activation_store {H : Type} {program : Program} {base live : Store H}
    {a : MemAddr} {initial : MemInst} (checked : program.checkV1 a = true)
    (layout : Layout program base a initial) {address : FuncAddr} {fn : Function}
    (found : program.lookup address = some fn) (shared : SharedStore base a initial live)
    {caller : Frame} {locals callerSaved saved : List Value} {callerTail tail : List Admin}
    {offset : Fin (2 ^ 32)} {ptr : BitVec 32} {dst : Config H}
    (move : Step CallFrame.v1NoHost ⟨live, caller,
      MemoryWrite.v1ActivationCode fn.declaration.results.head? (Graph.currentFrame fn.declaration locals)
        callerSaved callerTail (values saved ++ [.source (.intConst .i32 ptr),
          .source ((Op.load offset).v1)] ++ tail)⟩ dst) :
    dst.store = live ∧ dst.frame = caller := by
  obtain ⟨bytes, _, rfl⟩ := shared
  obtain ⟨_, _, rfl⟩ := (MemoryWrite.v1_activation_load_step_iff_at
    (immediate := immediate offset) (address := ptr) (saved := saved) (tail := tail)
    (frame_memory checked layout found locals bytes)).mp move
  exact ⟨rfl, rfl⟩

theorem exit_store {H : Type} {s : Store H} {caller callee : Frame} {arity : Nat}
    {saved : List Value} {tail : List Admin} {result : Nested.Result} {dst : Config H}
    (move : Step CallFrame.v1NoHost
      ⟨s, caller, values saved ++ .frame arity callee (Nested.resultCode values .trap result) :: tail⟩ dst) :
    dst.store = s ∧ dst.frame = caller := by
  obtain ⟨outer, inside | ⟨_, _, same, _⟩⟩ := move.frame_inv (p := saved) (q := tail)
    (n := arity) (fr := callee) (body := Nested.resultCode values .trap result) rfl
  · obtain ⟨_, _, inner, _⟩ := inside
    have projected := inner.toLime (target := CallFrame.limeNoHost) (fun _ _ _ _ h => h)
    have mapResult : codeToLime (Nested.resultCode values .trap result) =
        Nested.resultCode Wasm.Lime1.Execution.values .trap result := by
      cases result with
      | values => exact map_values _
      | trap => rfl
    exact (Nested.lime_result_stuck (r := result)
      (by simpa only [Config.toLime, mapResult] using projected)).elim
  · exact ⟨same.symm, outer⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Proofs
