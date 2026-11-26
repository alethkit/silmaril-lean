module

import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Thms
import Silmaril.Wasm.V1.Execution.Properties
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
  ⟨{ declaration [childAddr] [.int .i32] with params := [.int .i64] }, 1, [i32 2], [.ranked (.call (target traps)), .load 1]⟩
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
private theorem returnedWrite : Steps CallFrame.v1NoHost (calling false)
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
private theorem trapRun : Steps CallFrame.v1NoHost (calling true) ⟨written true, caller true, [.trap]⟩ := by
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

-- The ordinary outer call enters the reader with its i64 argument. The
-- reader's call then opens the writer inside that already-live activation.
private def outside : Frame := ⟨[i32 88], { funcs := [parentAddr] }⟩
private def rootArgs := [Value.int .i64 9]
private def rootInput : State := ⟨before, outside, values rootArgs ++ [.source (.call ⟨0⟩)]⟩

private def inReader (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩

example : Step CallFrame.v1NoHost (render (base false) slot memory rootInput)
    (render (base false) slot memory ⟨before, outside, values rootArgs ++ [.invoke parentAddr]⟩) := by
  have ready := call_ready (p := program false) (m := slot) (addr := parentAddr) (fn := reader false)
    (index := ⟨0⟩) (caller := outside) rfl rfl rootArgs before
  have move : Edge (program false) slot rootInput
      ⟨before, outside, values rootArgs ++ [.invoke parentAddr]⟩ :=
    .context (.resolve (i := ⟨0⟩) rfl) rootArgs []
  exact (v1_step_iff (checked false) (layout false) ready).mpr
    ⟨_, move, move.ready (checked false) ready, rfl⟩

private theorem rootEnter (traps : Bool) : Steps CallFrame.v1NoHost
    ⟨base traps, outside, rootInput.code⟩ (inReader (calling traps)) := by
  apply Relation.ReflTransGen.head
    (b := ⟨base traps, outside, values rootArgs ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) rootArgs [])
  exact .single ((layout traps).enter (checked traps) (address := parentAddr) (fn := reader traps) rfl
    (layout traps).initial_shared (saved := []) (args := rootArgs) (tail := []) rfl)

private def returned : Config Unit := ⟨written false, outside, values [i32 0x11223344]⟩
private def unwound : Config Unit := ⟨written true, outside, [.trap]⟩

private theorem rootReturns : Steps CallFrame.v1NoHost ⟨base false, outside, rootInput.code⟩ returned := by
  have body := (returnedWrite.label 1 []).frame 1 outside
  have finishLabel : Step CallFrame.v1NoHost
      (inReader ⟨written false, caller false, values [i32 0x11223344]⟩)
      ⟨written false, outside, [.frame 1 (caller false) (values [i32 0x11223344])]⟩ :=
    .frame (.pure _ _ (.labelDone 1 [] [i32 0x11223344])) 1 _
  have finishFrame : Step CallFrame.v1NoHost
      ⟨written false, outside, [.frame 1 (caller false) (values [i32 0x11223344])]⟩ returned :=
    .pure _ _ (.frameDone 1 (caller false) [i32 0x11223344] rfl)
  exact (((rootEnter false).trans body).tail finishLabel).tail finishFrame

private theorem rootTraps : Steps CallFrame.v1NoHost ⟨base true, outside, rootInput.code⟩ unwound := by
  have body := (trapRun.label 1 []).frame 1 outside
  have finishLabel : Step CallFrame.v1NoHost (inReader ⟨written true, caller true, [.trap]⟩)
      ⟨written true, outside, [.frame 1 (caller true) [.trap]]⟩ :=
    .frame (.pure _ _ (.labelTrap 1 [])) 1 _
  have finishFrame : Step CallFrame.v1NoHost
      ⟨written true, outside, [.frame 1 (caller true) [.trap]]⟩ unwound :=
    .pure _ _ (.frameTrap 1 (caller true))
  exact (((rootEnter true).trans body).tail finishLabel).tail finishFrame

private theorem rootPrefix : Steps CallFrame.v1NoHost
    ⟨base true, outside, rootInput.code⟩ (inReader nextWrite) := by
  have body := ((Relation.ReflTransGen.single (resolve true)).tail (enter true)).tail writesBeforeTrap
  exact (rootEnter true).trans ((Wasm.V1.Execution.Steps.label body 1 []).frame 1 outside)

private theorem rootReadback {traps : Bool} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨base traps, outside, rootInput.code⟩ dst) :
    ∃ out, Runs (program traps) slot rootInput out ∧
      Ready (program traps) slot 2 before.size out ∧ dst = render (base traps) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := reader traps) (index := ⟨0⟩) (args := rootArgs) (caller := outside)
    (checked traps) (layout traps) rfl rfl).mp path

example : ∃ out, Runs (program false) slot rootInput out ∧ returned = render (base false) slot memory out := by
  obtain ⟨out, path, _, eq⟩ := rootReadback rootReturns
  exact ⟨out, path, eq⟩

example : ∃ out, Runs (program true) slot rootInput out ∧ unwound = render (base true) slot memory out ∧
    SharedStore (base true) slot memory unwound.store := by
  obtain ⟨out, path, ready, eq⟩ := rootReadback rootTraps
  exact ⟨out, path, eq, eq ▸ render_shared ready⟩

-- Stop after the nested write with both activations still live. Reflect the
-- very next bounds trap separately, with the written store still in place.
example : ∃ middle stopped,
    Runs (program true) slot rootInput middle ∧ Edge (program true) slot middle stopped ∧
      inReader nextWrite = render (base true) slot memory middle ∧
      inReader firstTrap = render (base true) slot memory stopped ∧ middle.bytes = stopped.bytes := by
  obtain ⟨middle, path, ready, endpoint⟩ := rootReadback rootPrefix
  have trapUnderReader := Step.frame (Step.label trapsLater 1 []) 1 outside
  have trapFromRender : Step CallFrame.v1NoHost (render (base true) slot memory middle) (inReader firstTrap) :=
    endpoint ▸ trapUnderReader
  obtain ⟨stopped, move, _, eq⟩ := (v1_step_iff (checked true) (layout true) ready).mp trapFromRender
  have storeBefore := congrArg (fun c : Config Unit => c.store) endpoint
  have storeAfter := congrArg (fun c : Config Unit => c.store) eq
  have sameStore := storeBefore.symm.trans storeAfter
  have sameCell := congrArg (fun s : Store Unit => s.memories[slot.value]?) sameStore
  have inBounds : slot.value < (base true).memories.length := by decide
  have cell : ({ memory with data := middle.bytes } : MemInst) =
      { memory with data := stopped.bytes } := by
    simpa [render, storeWithBytes, Wasm.V1.Execution.setMemory, List.getElem?_set, inBounds] using sameCell
  exact ⟨middle, stopped, path, move, endpoint, eq, congrArg MemInst.data cell⟩

-- The surrounding address stays below the condition and outside the arm.
-- The false arm skips the entire call, even when that callee would write and trap.
private def conditional (traps : Bool) : Function :=
  ⟨{ declaration [childAddr] [.int .i32] with params := [.int .i32] }, 1, [i32 2],
    [.ranked (.numeric (.get ⟨0⟩)), .if_ none [.ranked (.call (target traps))] [], .load 1]⟩

private def ifProgram (traps : Bool) : Program := ⟨[some (writer traps), some (conditional traps)]⟩
private def ifBase (traps : Bool) : Store Unit :=
  { memories := [untouched, memory], funcs := [writer traps, conditional traps].map
      (fun fn => .wasm fn.declaration.type fn.declaration.module fn.v1Func) }
private theorem ifChecked (traps : Bool) : (ifProgram traps).checkV1 slot = true := by
  cases traps <;> rfl
private theorem ifLayout (traps : Bool) : Layout (ifProgram traps) (ifBase traps) slot memory where
  memory := rfl
  functions := by
    intro a fn found
    rcases a with ⟨_ | _ | n⟩ <;> simp [Program.lookup, ifProgram] at found
    all_goals subst fn; rfl

example : Function.checkV1 { conditional false with
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ none [] [.store 0], .load 1] } slot = false := rfl

example : Function.checkV1 { conditional false with
    declaration := { (conditional false).declaration with params := [.int .i64] } } slot = false := rfl

example : Function.checkV1 { conditional false with
    initial := []
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ (some (.int .i32))
      [.ranked (.numeric (.get ⟨0⟩))]
      [.if_ (some (.int .i32)) [] []]] } slot = false := rfl

-- The inner arm may return the function's i32 even though its label is void.
example : Function.checkV1 { conditional false with
    initial := []
    code := [.ranked (.numeric (.get ⟨0⟩)), .if_ (some (.int .i32))
      [.ranked (.numeric (.get ⟨0⟩)), .if_ none
        [.ranked (.numeric (.get ⟨0⟩)), .ranked .return_] [],
        .ranked (.numeric (.get ⟨0⟩))]
      [.ranked (.numeric (.get ⟨0⟩))]] } slot = true := rfl

example : (Program.mk [some (writer false), some { conditional false with rank := 0 }]).checkV1 slot =
    false := rfl

private def ifInput (condition : BitVec 32) : State :=
  ⟨before, outside, values [i32 condition] ++ [.source (.call ⟨0⟩)]⟩
private def ifFrame (traps : Bool) (condition : BitVec 32) : Frame :=
  (conditional traps).declaration.frame [i32 condition]
private def underIfReader (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] c.code]]⟩
private def selected (condition : BitVec 32) : Wasm.V1.Expr :=
  if condition = 0 then [] else [.call ⟨0⟩]
private def ifWritten (traps : Bool) := storeWithBytes (ifBase traps) slot memory after

-- Stop at the selected block, then account for the separate native label step.
private theorem ifSelect (traps : Bool) (condition : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩
      (underIfReader ⟨ifBase traps, ifFrame traps condition,
        values saved ++ [.source (.block none (selected condition))] ++ continuation⟩) := by
  apply Relation.ReflTransGen.head
    (b := ⟨ifBase traps, outside, values [i32 condition] ++ [.invoke parentAddr]⟩)
    (Step.context (.call _ _ ⟨0⟩ parentAddr rfl) [i32 condition] [])
  have invoke := (ifLayout traps).enter (ifChecked traps) (address := parentAddr)
    (fn := conditional traps) rfl
    (ifLayout traps).initial_shared (caller := outside) (saved := []) (args := [i32 condition]) (tail := []) rfl
  refine Relation.ReflTransGen.head invoke ?_
  refine Relation.ReflTransGen.head
    (Step.frame (Step.label
      (Step.context (.localGet _ _ ⟨0⟩ (i32 condition) rfl) saved
        ([.source (.if_ none [.call ⟨0⟩] [])] ++ continuation)) 1 []) 1 outside) ?_
  exact .single (.frame (.label ((v1_if_select_iff (saved := saved)).mpr rfl) 1 []) 1 outside)

private theorem ifOpen (traps : Bool) (condition : BitVec 32) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩
      (underIfReader ⟨ifBase traps, ifFrame traps condition,
        values saved ++ [.label 0 [] (Wasm.V1.Execution.expression (selected condition))] ++ continuation⟩) :=
  (ifSelect traps condition).tail
    (.frame (.label (.context (.pure _ _ (.block none (selected condition))) saved continuation) 1 []) 1 outside)

private theorem ifReadback {traps : Bool} {condition : BitVec 32} {dst : Config Unit}
    (path : Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput condition).code⟩ dst) :
    ∃ out, Runs (ifProgram traps) slot (ifInput condition) out ∧
      Ready (ifProgram traps) slot 2 before.size out ∧ dst = render (ifBase traps) slot memory out :=
  (v1_call_run_iff (root := parentAddr) (fn := conditional traps) (index := ⟨0⟩)
    (args := [i32 condition]) (caller := outside) (ifChecked traps) (ifLayout traps) rfl rfl).mp path

example : ∃ out, Runs (ifProgram false) slot (ifInput 1) out ∧
    underIfReader ⟨ifBase false, ifFrame false 1,
      values saved ++ [.source (.block none [.call ⟨0⟩])] ++ continuation⟩ =
        render (ifBase false) slot memory out := by
  obtain ⟨out, path, _, eq⟩ := ifReadback (ifSelect false 1)
  exact ⟨out, path, eq⟩

private theorem ifFinish {traps : Bool} {condition word : BitVec 32} {s : Store Unit}
    (load : Step CallFrame.v1NoHost
      ⟨s, ifFrame traps condition, values saved ++ continuation⟩
      ⟨s, ifFrame traps condition, values [i32 word]⟩) :
    Steps CallFrame.v1NoHost
      (underIfReader ⟨s, ifFrame traps condition, values saved ++ [.label 0 [] []] ++ continuation⟩)
      ⟨s, outside, values [i32 word]⟩ := by
  apply Relation.ReflTransGen.head
    (Step.frame (Step.label (Step.context (.pure _ _ (.labelDone 0 [] [])) saved continuation) 1 []) 1 outside)
  apply Relation.ReflTransGen.head (Step.frame (Step.label load 1 []) 1 outside)
  apply Relation.ReflTransGen.head (Step.frame (.pure _ _ (.labelDone 1 [] [i32 word])) 1 outside)
  exact .single (.pure _ _ (.frameDone 1 (ifFrame traps condition) [i32 word] rfl))

example : ∃ out, Runs (ifProgram true) slot (ifInput 0) out ∧
    (⟨ifBase true, outside, values [i32 0]⟩ : Config Unit) = render (ifBase true) slot memory out := by
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 1) (address := 2)
    (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (ifBase true) (ifFrame true 0) = some (slot, memory) from rfl)).mpr
    ⟨.value 0, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  obtain ⟨out, path, _, eq⟩ := ifReadback ((ifOpen true 0).trans (ifFinish load))
  exact ⟨out, path, eq⟩

private def inIfArm (traps : Bool) (c : Config Unit) : Config Unit :=
  underIfReader ⟨c.store, ifFrame traps 1, values saved ++ [.label 0 [] c.code] ++ continuation⟩

private theorem inIfArm_steps {traps : Bool} {a b : Config Unit}
    (path : Steps CallFrame.v1NoHost a b) (frame : a.frame = ifFrame traps 1)
    (frame' : b.frame = ifFrame traps 1) :
    Steps CallFrame.v1NoHost (inIfArm traps a) (inIfArm traps b) := by
  simpa only [inIfArm, underIfReader, frame, frame'] using
    ((((path.label 0 []).context saved continuation).label 1 []).frame 1 outside)

private theorem ifInvoke (traps : Bool) :
    Steps CallFrame.v1NoHost ⟨ifBase traps, outside, (ifInput 1).code⟩
      (inIfArm traps ⟨ifBase traps, ifFrame traps 1,
        MemoryWrite.v1ActivationCode none (callee traps) [] []
          (Wasm.V1.Execution.expression (writer traps).v1Func.body)⟩) := by
  apply (ifOpen traps 1).trans
  refine inIfArm_steps (traps := traps)
    (a := ⟨ifBase traps, ifFrame traps 1, [.source (.call ⟨0⟩)]⟩) ?_ rfl rfl
  apply Relation.ReflTransGen.head (Step.call _ _ ⟨0⟩ childAddr rfl)
  exact .single ((ifLayout traps).enter (ifChecked traps) (address := childAddr) (fn := writer traps) rfl
    (ifLayout traps).initial_shared (saved := []) (args := []) (tail := []) rfl)

example : ∃ out, Runs (ifProgram false) slot (ifInput 1) out ∧
    (⟨ifWritten false, outside, values [i32 0x11223344]⟩ : Config Unit) =
      render (ifBase false) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2) (callerSaved := []) (callerTail := []) (result := none)
    (caller := ifFrame false 1) (saved := []) (tail := [])
    (show Wasm.V1.Execution.frameMemory (ifBase false) (callee false) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have arm := ((Relation.ReflTransGen.single write).tail
    (Step.frame (.pure _ _ (.labelDone 0 [] [])) 0 (ifFrame false 1))).tail
    (Step.pure _ (ifFrame false 1) (.frameDone 0 (callee false) [] rfl))
  have resumed := (ifInvoke false).trans (inIfArm_steps arm rfl rfl)
  have load := (MemoryWrite.v1_context_load_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 1) (address := 2)
    (saved := []) (tail := [])
    ((ifLayout false).frame_memory (ifChecked false) (address := parentAddr) (fn := conditional false)
      rfl [i32 1] after)).mpr ⟨.value 0x11223344, MemoryQuery.fact_at (.load _ _ (by decide)), rfl⟩
  obtain ⟨out, path, _, eq⟩ := ifReadback (resumed.trans (ifFinish load))
  exact ⟨out, path, eq⟩

example : ∃ out, Runs (ifProgram true) slot (ifInput 1) out ∧
    (⟨ifWritten true, outside, [.trap]⟩ : Config Unit) = render (ifBase true) slot memory out := by
  have write := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2)
    (caller := ifFrame true 1) (callerSaved := []) (callerTail := []) (result := none)
    (saved := [i32 3, i32 0]) (tail := [.source ((Op.store 2).v1)])
    (show Wasm.V1.Execution.frameMemory (ifBase true) (callee true) = some (slot, memory) from rfl)).mpr
    ⟨.written after, writing, rfl⟩
  have fail := (MemoryWrite.v1_activation_store_step_iff_at (host := CallFrame.v1NoHost) (immediate := immediate 2) (callerSaved := []) (callerTail := []) (result := none)
    (caller := ifFrame true 1) (saved := []) (tail := []) (address := 3) (word := 0)
    (show Wasm.V1.Execution.frameMemory (ifWritten true) (callee true) = some (slot, updated) from rfl)).mpr
    ⟨.trap, MemoryWrite.store_trap_iff_at.mpr (by decide), rfl⟩
  have arm := (((Relation.ReflTransGen.single write).tail fail).tail
    (Step.frame (.pure _ _ (.labelTrap 0 [])) 0 (ifFrame true 1))).tail
    (Step.pure _ (ifFrame true 1) (.frameTrap 0 (callee true)))
  have branchTrap := ((ifInvoke true).trans (inIfArm_steps arm rfl rfl)).tail
    (Step.frame (Step.label (Step.context (.pure _ _ (.labelTrap 0 [])) saved continuation) 1 []) 1 outside)
  have discard := branchTrap.tail
    (Step.frame (Step.label (.pure _ _ (.trapValues (i32 2) [] continuation)) 1 []) 1 outside)
  have unwind := (discard.tail (Step.frame (.pure _ _ (.labelTrap 1 [])) 1 outside)).tail
    (Step.pure _ _ (.frameTrap 1 (ifFrame true 1)))
  obtain ⟨out, path, _, eq⟩ := ifReadback unwind
  exact ⟨out, path, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
