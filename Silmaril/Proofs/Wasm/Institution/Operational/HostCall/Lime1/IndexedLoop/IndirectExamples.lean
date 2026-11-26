module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms
import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IndirectExamples

open Execution.Runtime (Frame FuncInst MemInst TableInst Value)
open Wasm.Lime1.Execution
open Continuation (Label Op)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def num32 : NumType := .int .i32
private def num64 : NumType := .int .i64
private def expected : Wasm.Lime1.FuncType := ⟨[num64, num32], [num32, num64]⟩
private def wrong : Wasm.Lime1.FuncType := ⟨[num64, num32], [num64, num32]⟩
private def table : TableInst := ⟨[some ⟨3⟩, none, some ⟨4⟩], none⟩
private def indirect : IndirectSite := ⟨table, ⟨1⟩, expected⟩
private def prepare : Site Nat := ⟨⟨2⟩, ⟨[num64], [num64] ++ expected.params ++ [num32]⟩, 11⟩
private def target : Site Nat := ⟨⟨3⟩, expected, 12⟩
private def join : Site Nat := ⟨⟨5⟩, ⟨num64 :: expected.results, [num32]⟩, 14⟩
private def follow : Site Nat := ⟨⟨6⟩, ⟨[num64, num32], [num32]⟩, 15⟩
private def armTail : List (Op Nat) := [.call ⟨2⟩ join]
private def afterPrepare : List (Op Nat) := .callIndirect indirect :: armTail
private def arm : List (Op Nat) := .get ⟨0⟩ :: .call ⟨1⟩ prepare :: afterPrepare
private def afterArm : List (Op Nat) := [.call ⟨3⟩ follow]
private def label : Label Nat := ⟨.scalar num32, [i64 42], afterArm, none⟩

private def program : Program Nat where
  module := {
    types := [signature, expected]
    funcs := [⟨1⟩, ⟨2⟩, ⟨5⟩, ⟨6⟩]
    tables := [⟨0⟩]
    memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ (.scalar num32) arm arm :: afterArm
  saved := 42

private def base : Store Nat :=
  { memories := [initial], tables := [table], funcs :=
    [.wasm program.functionType program.module program.function, .host producerType 10,
      .host prepare.type prepare.code, .host expected 12, .host wrong 13,
      .host join.type join.code, .host follow.type follow.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl⟩
private def caller : Frame := ⟨[i32 9], {funcs := [⟨0⟩]}⟩
private abbrev Check := Continuation.Checked base program.module [num64]
private abbrev rootResults := [num32]

private theorem linked : indirect.Linked base program.module := by
  refine ⟨rfl, rfl, ?_⟩
  intro address member
  simp [indirect, table] at member
  rcases member with rfl | rfl
  · exact ⟨.host expected 12, rfl, fun _ => ⟨12, rfl⟩⟩
  · exact ⟨.host wrong 13, rfl, fun same => ((by decide : wrong ≠ expected) same).elim⟩

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  have afterLookup : Check [rootResults, rootResults] rootResults (num64 :: expected.results) armTail :=
    .call (site := join) (saved := []) rfl rfl .nil
  have atLookup : Check [rootResults, rootResults] rootResults
      (([num64] ++ expected.params) ++ [num32]) afterPrepare :=
    .callIndirect (site := indirect) (saved := [num64]) linked afterLookup
  have armChecked : Check [rootResults, rootResults] rootResults [] arm :=
    .get (type := num64) (stack := []) rfl (.call (site := prepare) (saved := []) rfl rfl atLookup)
  have tail : Check [rootResults] rootResults [num64, num32] afterArm :=
    .call (site := follow) (saved := []) rfl rfl .nil
  exact ⟨rfl, rfl, rfl, rfl, rfl, .if_ (type := .scalar num32) (saved := [num64]) rfl armChecked armChecked tail,
    rfl, rfl⟩

private def saved : List Value := [i64 99]
private def args : List Value := [i64 71, i32 21]
private def returned : List Value := [i32 33, i64 77]

private def host : HostSemantics Nat := fun id store operands outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ operands = [i64 7] ∧
      outcome = .returned (memory.store (bytes 1)) (.values [i32 1, i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ operands = [i64 7] ∧ ∃ selector : BitVec 32,
      outcome = .returned (memory.store (bytes 2)) (.values ((saved ++ args) ++ [i32 selector]))
  | 12 => store = memory.store (bytes 2) ∧ operands = args ∧
      outcome = .returned (memory.store (bytes 3)) (.values returned)
  | 13 => store = memory.store (bytes 2) ∧ operands = args ∧
      outcome = .returned (memory.store (bytes 9)) (.values [i64 77, i32 33])
  | 14 => store = memory.store (bytes 3) ∧ operands = saved ++ returned ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i32 44])
  | 15 => store = memory.store (bytes 4) ∧ operands = [i64 42, i32 44] ∧
      outcome = .returned (memory.store (bytes 5)) (.values [i32 55])
  | _ => False

private theorem indirectContract : indirect.Contract memory host := by
  intro address code member allocated
  simp [indirect, table] at member
  rcases member with rfl | rfl
  · change some (FuncInst.host expected 12 : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    have codeEq : 12 = code := (FuncInst.host.inj (Option.some.inj allocated)).2
    subst code
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  · change some (FuncInst.host wrong 13 : FuncInst Wasm.Lime1.Func Nat) =
      some (.host expected code) at allocated
    have bad : wrong = expected := congrArg FuncInst.type (Option.some.inj allocated)
    exact ((by decide : wrong ≠ expected) bad).elim

private theorem contract : program.Contract memory host := by
  have prepareContract : prepare.Contract memory host := by
    intro _ _ _ _ _ _ answer
    obtain ⟨_, _, selector, eq⟩ := answer
    cases eq
    exact ⟨bytes 2, rfl, rfl, rfl⟩
  have joinContract : join.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 4, rfl, rfl, rfl⟩
  have followContract : follow.Contract memory host := by
    intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 5, rfl, rfl, rfl⟩
  have armContract : Continuation.Contract memory host arm :=
    .get (.call prepareContract (.callIndirect indirectContract (.call joinContract .nil)))
  constructor
  · intro _ _ _ _ _ _ answer
    cases answer.2.2
    exact ⟨bytes 1, rfl, rfl, rfl⟩
  · exact .if_ armContract armContract (.call followContract .nil)

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩
private abbrev BodyPath (q : Continuation.State Nat) := Path ⟨q.bytes, .continuation q.phase q.labels⟩

private theorem BodyPath.step {a b : Continuation.State Nat} (path : BodyPath a)
    (move : Continuation.Edge memory host (program.active 7) rootResults a b) : BodyPath b :=
  path.tail (.continuation move)

private theorem atLookup (selector : BitVec 32) :
    BodyPath ⟨bytes 2, .source ((saved ++ args) ++ [i32 selector]) afterPrepare, [label]⟩ := by
  have producer : Path ⟨bytes 0, .producerInvoke 7⟩ :=
    ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
      (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))
  have returned : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩ ⟨bytes 1, .test 1 88 0⟩ :=
    .producerReturns rfl ⟨rfl, rfl, rfl⟩
  have exit : BodyPath ⟨bytes 1, .source [i64 42, i32 1] program.continuation, []⟩ :=
    (((producer.tail returned).tail (.control (.test 1 88 0))).tail
      (.control (.dropInput 1 88))).tail (.control (.loopResult 1))
  have inside : BodyPath ⟨bytes 1, .source [] arm, [label]⟩ :=
    (exit.step (.if_ (saved := [i64 42]) (args := []) (guard := 1) rfl)).step (.block rfl)
  have preparing : BodyPath ⟨bytes 1, .invoke [] prepare [i64 7] afterPrepare, [label]⟩ :=
    (inside.step (.get rfl)).step (.resolve (saved := []) (args := [i64 7]) rfl)
  exact preparing.step (.returned (vs := (saved ++ args) ++ [i32 selector]) rfl rfl ⟨rfl, rfl, selector, rfl⟩)

private theorem dispatched : BodyPath ⟨bytes 2, .invoke saved target args armTail, [label]⟩ := by
  have found : indirect.Lookup base 0 (some target) :=
    .host (address := ⟨3⟩) (code := 12) rfl (show target.Allocated base from rfl)
  exact (atLookup 0).step (.callIndirect (saved := saved) (args := args) rfl found)

-- Lookup leaves a pending invocation under the live label and the same bytes.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 99), value (i64 71), value (i32 21),
      .invoke ⟨3⟩, .source (.call ⟨2⟩)], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, dispatched, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, values [i32 55]⟩ := by
  have delivered : BodyPath ⟨bytes 3, .source (saved ++ returned) armTail, [label]⟩ :=
    dispatched.step (.returned (vs := returned) rfl rfl ⟨rfl, rfl, rfl⟩)
  have joined : BodyPath ⟨bytes 3, .invoke [] join (saved ++ returned) [], [label]⟩ :=
    delivered.step (.resolve (saved := []) (args := saved ++ returned) rfl)
  have result : BodyPath ⟨bytes 4, .source [i32 44] [], [label]⟩ :=
    joined.step (.returned (vs := [i32 44]) rfl rfl ⟨rfl, rfl, rfl⟩)
  have following : BodyPath ⟨bytes 4, .invoke [] follow [i64 42, i32 44] [], []⟩ :=
    (result.step .armResult).step (.resolve (saved := []) (args := [i64 42, i32 44]) rfl)
  have done : BodyPath ⟨bytes 5, .source [i32 55] [], []⟩ :=
    following.step (.returned (vs := [i32 55]) rfl rfl ⟨rfl, rfl, rfl⟩)
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (done.step .labelResult).step .frameDone, rfl, rfl⟩

private theorem lookupTrap {selector : BitVec 32} (failure : indirect.Lookup base selector none) :
    BodyPath ⟨bytes 2, .trapped (saved ++ args) (Continuation.code armTail), [label]⟩ :=
  (atLookup selector).step (.callIndirect (saved := saved) (args := args) rfl failure)

-- Lookup failure consumes the selector and preserves the arguments and suffix
-- until native trap cleanup. The mismatched host's own outcome is irrelevant.
example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 (program.active 7)
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 99), value (i64 71), value (i32 21),
      .trap, .source (.call ⟨2⟩)], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr
    ⟨_, lookupTrap (selector := 2) (.mismatch (fn := .host wrong 13) rfl rfl (by decide)), rfl, rfl⟩

example {dst : Config Nat} :
    Internal ⟨memory.store (bytes 2), program.active 7, values ((saved ++ args) ++ [i32 2]) ++
      .source (.callIndirect ⟨1⟩) :: Continuation.code armTail⟩ dst ↔
      dst = ⟨memory.store (bytes 2), program.active 7, values (saved ++ args) ++ .trap :: Continuation.code armTail⟩ :=
  IndirectSite.trap_iff (indirect := indirect) (selector := 2) linked (.mismatch (fn := .host wrong 13) rfl rfl (by decide))

private theorem unwind {selector : BitVec 32} (failure : indirect.Lookup base selector none) :
    Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ := by
  have inside : BodyPath ⟨bytes 2, .trapped [] [], [label]⟩ :=
    (lookupTrap failure).step (.erase (removed := saved ++ args) (cut := Continuation.code armTail)
      rfl rfl (.inl (by decide)))
  have outside : BodyPath ⟨bytes 2, .trapped [] [], []⟩ :=
    (inside.step .armTrap).step (.erase (removed := [i64 42]) (cut := Continuation.code afterArm)
      rfl rfl (.inl (by decide)))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, (outside.step .labelTrap).step .frameDone, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (selector := (-1)) (.bounds rfl)

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (selector := 1) (.null rfl)

example : Steps host launch ⟨memory.store (bytes 2), caller, [.trap]⟩ :=
  unwind (selector := 2) (.mismatch (fn := .host wrong 13) rfl rfl (by decide))

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IndirectExamples
