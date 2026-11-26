module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (Frame FuncAddr MemAddr MemInst Value)
open Wasm.V1.Execution (Config Step Steps Store values)

private abbrev i32 := Value.int .i32
private def before : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0, 0, 0, 0, 0xdd]⟩
private def after : ByteArray := ⟨#[0xaa, 0xbb, 0xcc, 0x44, 0x33, 0x22, 0x11, 0xdd]⟩
private def memory : MemInst := ⟨before, some 2⟩
private def untouched : MemInst := ⟨⟨#[3, 4]⟩, none⟩
private def slot : MemAddr := ⟨1⟩
private def childAddr : FuncAddr := ⟨0⟩
private def parentAddr : FuncAddr := ⟨1⟩

private def declaration (targets : List FuncAddr) (results : List NumType) : Declaration :=
  ⟨{ funcs := targets, memories := [slot] }, ⟨0⟩, [], [], results⟩

private def writer (traps : Bool) : Function :=
  ⟨declaration [] [], 0,
    (if traps then [i32 3, i32 0] else []) ++ [i32 1, i32 0x11223344],
    if traps then [.store 2, .store 2] else [.store 2]⟩
private def target (traps : Bool) : CallTarget := ⟨⟨0⟩, childAddr, (writer traps).declaration⟩
private def reader (traps : Bool) : Function :=
  ⟨declaration [childAddr] [.int .i32], 1, [i32 2], [.ranked (.call (target traps)), .load 1]⟩
private def program (traps : Bool) : Program := ⟨[some (writer traps), some (reader traps)]⟩

private theorem checked (traps : Bool) : (program traps).checkV1 slot = true := by cases traps <;> rfl

example : (program false).checkV1 ⟨0⟩ = false := rfl

example : (Program.mk [some (writer false), some { reader false with rank := 0 }]).checkV1 slot = false :=
  rfl

example : ({ writer false with initial := [Value.int .i64 1, i32 0] } : Function).checkV1 slot = false :=
  rfl

example : Function.checkV1 { writer false with code := [.ranked .unreachable, .ranked (.block none [])] }
    slot = false := rfl

example : Function.checkV1 { reader false with declaration := declaration [childAddr] [.int .i32, .int .i32] }
    slot = false := rfl

example : Function.checkV1 { reader false with initial := [Value.int .i64 2] } slot = false := rfl

private theorem resolves (traps : Bool) : (reader traps).declaration.module.funcs[0]? = some childAddr :=
  (Program.linked_target (checked traps) (address := parentAddr) (fn := reader traps) rfl (target := target traps)
    (by simp [reader, Function.targets, Op.targets, Graph.Op.targets])).choose_spec.2.1

private def base (traps : Bool) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer traps, reader traps].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }

private theorem layout (traps : Bool) : Layout (program traps) (base traps) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, program] at found
    all_goals subst fn; rfl

example : ¬ Layout (program false) { base false with memories := [] } slot memory := by
  intro missing
  cases missing.memory

private def caller (traps : Bool) : Frame :=
  Graph.currentFrame (reader traps).declaration [Value.int .i64 9]
private def callee (traps : Bool) : Frame := (writer traps).declaration.frame []
private def saved := [i32 2]
private def continuation : List Wasm.V1.Execution.Admin := [.source ((Op.load 1).v1)]
private def written (traps : Bool) := storeWithBytes (base traps) slot memory after
private def updated : MemInst := { memory with data := after }

private def armed (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, MemoryWrite.v1ActivationCode none (callee traps) saved continuation
    (Wasm.V1.Execution.expression (writer traps).v1Func.body)⟩
private def pending (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, values saved ++ .invoke childAddr :: continuation⟩

private def calling (traps : Bool) : Config Unit :=
  ⟨base traps, caller traps, values saved ++ .source (.call ⟨0⟩) :: continuation⟩

private theorem resolve (traps : Bool) : Step CallFrame.v1NoHost (calling traps) (pending traps) :=
  .context (.call _ _ ⟨0⟩ childAddr (resolves traps)) saved continuation

private theorem enter (traps : Bool) : Step CallFrame.v1NoHost (pending traps) (armed traps) :=
  (layout traps).enter (checked traps) (address := childAddr) (fn := writer traps) rfl
    (layout traps).initial_shared (saved := saved) (args := []) (tail := continuation) rfl

private theorem writing : MemoryWrite.EdgeAt before 2 (.store 1 0x11223344) (.written after) :=
  MemoryWrite.fact_at (.write _ _ _ (by decide))

private theorem didWrite : Step CallFrame.v1NoHost (armed false)
    ⟨written false, caller false, MemoryWrite.v1ActivationCode none (callee false) saved continuation []⟩ :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (base false) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩

example : SharedStore (base false) slot memory (written false) :=
  ((layout false).store_activation_shared (checked false) (address := childAddr) (fn := writer false) rfl
    (layout false).initial_shared (locals := []) (saved := []) (offset := 2)
    (callerSaved := saved) (callerTail := continuation) (tail := []) (ptr := 1) (word := 0x11223344) didWrite).1

-- Return to the parent's selected memory and observe the differently offset load.
example : Steps CallFrame.v1NoHost (calling false)
    ⟨written false, caller false, values [i32 0x11223344]⟩ := by
  apply Relation.ReflTransGen.head (resolve false)
  apply Relation.ReflTransGen.head (enter false)
  apply Relation.ReflTransGen.head didWrite
  apply Relation.ReflTransGen.head
    (b := ⟨written false, caller false, values saved ++ [.frame 0 (callee false) []] ++ continuation⟩)
    (Step.context (.frame (.pure _ _ (.labelDone 0 [] [])) 0 _) saved continuation)
  apply Relation.ReflTransGen.head
    (b := ⟨written false, caller false, values saved ++ continuation⟩)
    (Step.context (.pure _ _ (.frameDone 0 (callee false) [] rfl)) saved continuation)
  have current := (layout false).frame_memory (checked false) (address := parentAddr) (fn := reader false)
    rfl [Value.int .i64 9] after
  exact .single ((MemoryWrite.v1_context_load_step_iff_at (immediate := immediate 1) (address := 2)
    (saved := []) (tail := []) current).mpr ⟨.value 0x11223344,
      MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩)

private def laterStore : List Wasm.V1.Execution.Admin :=
  [.source (.intConst .i32 3), .source (.intConst .i32 0), .source ((Op.store 2).v1)]
private def nextWrite : Config Unit :=
  ⟨written true, caller true, MemoryWrite.v1ActivationCode none (callee true) saved continuation laterStore⟩
private def firstTrap : Config Unit :=
  ⟨written true, caller true, MemoryWrite.v1ActivationCode none (callee true) saved continuation [.trap]⟩

private theorem writesBeforeTrap : Step CallFrame.v1NoHost (armed true) nextWrite :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := [i32 3, i32 0])
    (tail := [.source ((Op.store 2).v1)])
    (show Wasm.V1.Execution.frameMemory (base true) (callee true) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩

private theorem trapsLater : Step CallFrame.v1NoHost nextWrite firstTrap :=
  (MemoryWrite.v1_activation_store_step_iff_at (immediate := immediate 2) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (written true) (callee true) = some (slot, updated) from rfl)).mpr
    ⟨.trap, MemoryWrite.store_trap_iff_at.mpr (by decide), rfl⟩

example : SharedStore (base true) slot memory firstTrap.store :=
  ((layout true).store_activation_shared (checked true) (address := childAddr) (fn := writer true) rfl
    (SharedStore.write rfl writing) (locals := []) (callerSaved := saved) (callerTail := continuation)
    (saved := []) (tail := []) (offset := 2) (ptr := 3) (word := 0) trapsLater).1

-- The later bounds failure preserves the first write through label and frame
-- unwind, including the native step that skips the parent's pending load.
example : Steps CallFrame.v1NoHost (calling true) ⟨written true, caller true, [.trap]⟩ := by
  apply Relation.ReflTransGen.head (resolve true)
  apply Relation.ReflTransGen.head (enter true)
  apply Relation.ReflTransGen.head writesBeforeTrap
  apply Relation.ReflTransGen.head trapsLater
  apply Relation.ReflTransGen.head
    (b := ⟨written true, caller true, values saved ++ [.frame 0 (callee true) [.trap]] ++ continuation⟩)
    (Step.context (.frame (.pure _ _ (.labelTrap 0 [])) 0 _) saved continuation)
  apply Relation.ReflTransGen.head
    (b := ⟨written true, caller true, values saved ++ [.trap] ++ continuation⟩)
    (Step.context (.pure _ _ (.frameTrap 0 (callee true))) saved continuation)
  exact .single (.pure _ _ (.trapValues (i32 2) [] continuation))

example : (written true).memories = [untouched, updated] ∧ (written true).funcs = (base true).funcs :=
  ⟨rfl, rfl⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
