module

import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Thms

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IfExamples

open Execution.Runtime (Frame MemInst)
open Wasm.Lime1.Execution
open Continuation (Op)
open Continuation.Conditional (Choice)

private def bytes (mark : UInt8) : ByteArray := ⟨#[0xaa, mark, 0xbb]⟩
private def initial : MemInst := ⟨bytes 0, none⟩
private def left : Site Nat := ⟨⟨2⟩, signature, 11⟩
private def right : Site Nat := ⟨⟨3⟩, signature, 12⟩
private def join : Site Nat := ⟨⟨4⟩, ⟨[.int .i64, .int .i32], [.int .i32]⟩, 13⟩

private def choice : Choice Nat :=
  ⟨.int .i32, [.get ⟨0⟩, .call ⟨1⟩ left], [.get ⟨0⟩, .call ⟨2⟩ right], [.call ⟨3⟩ join]⟩

private def program : Program Nat where
  module := { types := [signature], funcs := [⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩], memories := [⟨0⟩] }
  rootAddress := ⟨0⟩
  loopIndex := ⟨0⟩
  producerIndex := ⟨0⟩
  producerAddress := ⟨1⟩
  producerCode := 10
  continuation := .if_ choice
  saved := 42

private def base : Store Nat :=
  { memories := [initial], funcs := [.wasm signature program.module program.function, .host producerType 10,
      .host left.type left.code, .host right.type right.code, .host join.type join.code] }

private def memory : Memory32 base := ⟨⟨0⟩, initial, rfl⟩
private def caller : Frame := ⟨[i32 99], { funcs := [⟨0⟩] }⟩

private theorem checked : program.Checked memory caller ⟨0⟩ := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, rfl⟩
  · exact .get (stack := []) (type := .int .i64) rfl
      (.call (base := base) (site := left) (saved := []) rfl rfl .nil)
  · exact .get (stack := []) (type := .int .i64) rfl
      (.call (base := base) (site := right) (saved := []) rfl rfl .nil)
  · exact .call (base := base) (site := join) (saved := []) rfl rfl .nil

private def guardValue (takeLeft : Bool) : BitVec 32 := if takeLeft then 1 else 0
private def loopBytes (takeLeft : Bool) : ByteArray := bytes (if takeLeft then 1 else 2)

private def host : HostSemantics Nat := fun id store args outcome =>
  match id with
  | 10 => store = memory.store (bytes 0) ∧ args = [i64 7] ∧ ∃ flag : Bool,
      outcome = .returned (memory.store (loopBytes flag)) (.values [i32 (guardValue flag), i64 88, i32 0])
  | 11 => store = memory.store (bytes 1) ∧ args = [i64 7] ∧
      (outcome = .returned (memory.store (bytes 3)) (.values [i32 31]) ∨
       outcome = .returned (memory.store (bytes 5)) .trap)
  | 12 => store = memory.store (bytes 2) ∧ args = [i64 7] ∧
      outcome = .returned (memory.store (bytes 4)) (.values [i32 47])
  | 13 => (store = memory.store (bytes 3) ∧ args = [i64 42, i32 31] ∧
      outcome = .returned (memory.store (bytes 6)) (.values [i32 51])) ∨
      (store = memory.store (bytes 4) ∧ args = [i64 42, i32 47] ∧
      outcome = .returned (memory.store (bytes 7)) (.values [i32 52]))
  | _ => False

private theorem leftContract : left.Contract memory host := by
  intro live args returned outcome _ _ answer
  change host 11 (memory.store live) args (.returned returned outcome) at answer
  rcases answer.2.2 with eq | eq
  · cases eq
    exact ⟨bytes 3, rfl, rfl, rfl⟩
  · cases eq
    exact ⟨bytes 5, rfl, rfl, trivial⟩

private theorem rightContract : right.Contract memory host := by
  intro live args returned outcome _ _ answer
  change host 12 (memory.store live) args (.returned returned outcome) at answer
  cases answer.2.2
  exact ⟨bytes 4, rfl, rfl, rfl⟩

private theorem joinContract : join.Contract memory host := by
  intro live args returned outcome _ _ answer
  change host 13 (memory.store live) args (.returned returned outcome) at answer
  rcases answer with ⟨_, _, eq⟩ | ⟨_, _, eq⟩
  · cases eq
    exact ⟨bytes 6, rfl, rfl, rfl⟩
  · cases eq
    exact ⟨bytes 7, rfl, rfl, rfl⟩

private theorem contract : program.Contract memory host := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro live args returned outcome _ _ answer
    change host 10 (memory.store live) args (.returned returned outcome) at answer
    obtain ⟨_, _, flag, eq⟩ := answer
    cases eq
    refine ⟨loopBytes flag, ?_, rfl, rfl⟩
    cases flag <;> rfl
  · intro index site found
    have eq : Op.call index site = .call ⟨1⟩ left := by
      simpa only [choice, List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or, or_false] using found
    cases eq
    exact leftContract
  · intro index site found
    have eq : Op.call index site = .call ⟨2⟩ right := by
      simpa only [choice, List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or, or_false] using found
    cases eq
    exact rightContract
  · intro index site found
    have eq : Op.call index site = .call ⟨3⟩ join := by
      simpa only [choice, List.mem_cons, List.not_mem_nil, or_false] using found
    cases eq
    exact joinContract

private def launch : Config Nat := ⟨base, caller, values [i64 7] ++ [.source (.call ⟨0⟩)]⟩
private abbrev Path := Relation.ReflTransGen (Edge program memory host 7) ⟨bytes 0, .source⟩

private theorem firstInvoke : Path ⟨bytes 0, .producerInvoke 7⟩ :=
  ((((Relation.ReflTransGen.single (.control .resolve)).tail (.control .enter)).tail
    (.control .readLocal)).tail (.control (.openLoop 7))).tail (.control (.resolveProducer 7))

private theorem selects (flag : Bool) :
    Path ⟨loopBytes flag, .continuation (.block [i64 42] (guardValue flag) choice)⟩ := by
  have answer : Edge program memory host 7 ⟨bytes 0, .producerInvoke 7⟩
      ⟨loopBytes flag, .test (guardValue flag) 88 0⟩ :=
    .producerReturns (by cases flag <;> rfl) ⟨rfl, rfl, flag, rfl⟩
  exact ((((firstInvoke.tail answer).tail (.control (.test (guardValue flag) 88 0))).tail
    (.control (.dropInput (guardValue flag) 88))).tail (.control (.loopResult (guardValue flag)))).tail
    (.continuation .select)

-- Selection consumes the actual i32 result of the loop and exposes just
-- the chosen source block before its separate label entry.
example : Steps host launch ⟨memory.store (bytes 1), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .source (.block (.value (.int .i32)) [.localGet ⟨0⟩, .call ⟨1⟩]),
      .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, selects true, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 2), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .source (.block (.value (.int .i32)) [.localGet ⟨0⟩, .call ⟨2⟩]),
      .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, selects false, rfl, rfl⟩

private theorem inLeft : Path ⟨bytes 1, .continuation (.arm [i64 42] choice (.invoke [] left [i64 7] []))⟩ :=
  (((selects true).tail (.continuation .enter)).tail (.continuation (.arm (.get rfl)))).tail
    (.continuation (.arm (.resolve (site := left) (saved := []) (args := [i64 7]) rfl)))

private theorem inRight : Path ⟨bytes 2, .continuation (.arm [i64 42] choice (.invoke [] right [i64 7] []))⟩ :=
  (((selects false).tail (.continuation .enter)).tail (.continuation (.arm (.get rfl)))).tail
    (.continuation (.arm (.resolve (site := right) (saved := []) (args := [i64 7]) rfl)))

-- The host runs with the arm's own stack. The saved i64 is outside its label.
example : Steps host launch ⟨memory.store (bytes 1), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .label 1 [] [value (i64 7), .invoke ⟨2⟩], .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, inLeft, rfl, rfl⟩

private theorem joinLeft : Path ⟨bytes 3, .continuation (.tail (.source [i64 42, i32 31] choice.tail))⟩ := by
  have answer : Edge program memory host 7
      ⟨bytes 1, .continuation (.arm [i64 42] choice (.invoke [] left [i64 7] []))⟩
      ⟨bytes 3, .continuation (.arm [i64 42] choice (.source [i32 31] []))⟩ :=
    .continuation (.arm (.returned (host := host) (mem := memory) (next := bytes 3) (site := left) (vs := [i32 31]) (saved := []) (ops := [])
      rfl rfl ⟨rfl, rfl, .inl rfl⟩))
  exact (inLeft.tail answer).tail (.continuation (.arm .labelResult))

private theorem joinRight : Path ⟨bytes 4, .continuation (.tail (.source [i64 42, i32 47] choice.tail))⟩ := by
  have answer : Edge program memory host 7
      ⟨bytes 2, .continuation (.arm [i64 42] choice (.invoke [] right [i64 7] []))⟩
      ⟨bytes 4, .continuation (.arm [i64 42] choice (.source [i32 47] []))⟩ :=
    .continuation (.arm (.returned (host := host) (mem := memory) (next := bytes 4) (site := right) (vs := [i32 47]) (saved := []) (ops := [])
      rfl rfl ⟨rfl, rfl, rfl⟩))
  exact (inRight.tail answer).tail (.continuation (.arm .labelResult))

example : Steps host launch ⟨memory.store (bytes 3), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), value (i32 31), .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, joinLeft, rfl, rfl⟩

private theorem finish {live next : ByteArray} {input out : BitVec 32}
    (path : Path ⟨live, .continuation (.tail (.source [i64 42, i32 input] choice.tail))⟩)
    (liveNext : memory.Live next)
    (answer : host 13 (memory.store live) [i64 42, i32 input]
      (.returned (memory.store next) (.values [i32 out]))) :
    Path ⟨next, .continuation (.tail (.done (.values [i32 out])))⟩ := by
  have pending : Path ⟨live, .continuation (.tail (.invoke [] join [i64 42, i32 input] []))⟩ :=
    path.tail (.continuation (.tail (.resolve (site := join) (args := [i64 42, i32 input]) (saved := []) rfl)))
  have returns : Edge program memory host 7 ⟨live, .continuation (.tail (.invoke [] join [i64 42, i32 input] []))⟩
      ⟨next, .continuation (.tail (.source [i32 out] []))⟩ :=
    .continuation (.tail (.returned liveNext rfl answer))
  exact ((pending.tail returns).tail (.continuation (.tail .labelResult))).tail (.continuation (.tail .frameDone))

example : Steps host launch ⟨memory.store (bytes 6), caller, values [i32 51]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, finish (next := bytes 6) (out := 51) joinLeft rfl (.inl ⟨rfl, rfl, rfl⟩), rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 7), caller, values [i32 52]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, finish (next := bytes 7) (out := 52) joinRight rfl (.inr ⟨rfl, rfl, rfl⟩), rfl, rfl⟩

private theorem leftTrap : Path ⟨bytes 5, .continuation (.tail (.trapped [i64 42] (Continuation.code choice.tail)))⟩ := by
  have answer : Edge program memory host 7
      ⟨bytes 1, .continuation (.arm [i64 42] choice (.invoke [] left [i64 7] []))⟩
      ⟨bytes 5, .continuation (.arm [i64 42] choice (.trapped [] []))⟩ :=
    .continuation (.arm (.trapped (host := host) (mem := memory) (next := bytes 5) (site := left) (saved := []) (ops := [])
      rfl ⟨rfl, rfl, .inr rfl⟩))
  exact (inLeft.tail answer).tail (.continuation (.arm .labelTrap))

example : Steps host launch ⟨memory.store (bytes 5), caller, [.frame 1 ⟨[i64 7], program.module⟩
    [.label 1 [] [value (i64 42), .trap, .source (.call ⟨3⟩)]]]⟩ :=
  (call_run_iff (arg := 7) checked contract).mpr ⟨_, leftTrap, rfl, rfl⟩

example : Steps host launch ⟨memory.store (bytes 5), caller, [.trap]⟩ := by
  have erase : Edge program memory host 7
      ⟨bytes 5, .continuation (.tail (.trapped [i64 42] (Continuation.code choice.tail)))⟩
      ⟨bytes 5, .continuation (.tail (.trapped [] []))⟩ :=
    .continuation (.tail (.erase (removed := [i64 42]) (cut := Continuation.code choice.tail) rfl rfl (.inl (by decide))))
  have path := ((leftTrap.tail erase).tail (.continuation (.tail .labelTrap))).tail (.continuation (.tail .frameDone))
  exact (call_run_iff (arg := 7) checked contract).mpr ⟨_, path, rfl, rfl⟩

example : ¬ ({ choice with elseOps := [.get ⟨0⟩] }).Checked base program.module [.int .i64]
    signature.results [.int .i64] := by
  intro bad
  have wrong : Continuation.Checked base program.module [.int .i64] [.int .i32] [] [.get ⟨0⟩] := bad.elseArm
  generalize input : ([] : List NumType) = stack at wrong
  cases wrong with
  | get lookup tail =>
    have actual : some (.int .i64 : NumType) = some _ := lookup
    cases actual
    rw [← input] at tail
    generalize badType : ([.int .i64] : List NumType) = stack at tail
    cases tail
    cases badType

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.IfExamples
