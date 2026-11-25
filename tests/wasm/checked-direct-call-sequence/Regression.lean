module

import Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame Value)
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Numerics (Profile intBinOp)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence

open OuterCall.Computed

private abbrev i32 := Value.int .i32
private abbrev int32 := NumType.int .i32

private def firstCallee : CallFrame.Callee := ⟨{}, ⟨0⟩, [int32], [], some int32, .ret [i32 7]⟩
private def trappingCallee : CallFrame.Callee := { firstCallee with program := .unreachable }
private def secondCallee : CallFrame.Callee := ⟨{}, ⟨0⟩, [int32], [], some int32, .locals [.get ⟨0⟩]⟩
private def caller : Frame := ⟨[i32 5, i32 2], { funcs := [⟨0⟩, ⟨1⟩] }⟩
private def saved : List Value := [i32 3]

private def site (fn : CallFrame.Callee) : Site :=
  ⟨caller, [⟨⟨0⟩, ⟨0⟩, fn⟩, ⟨⟨1⟩, ⟨1⟩, secondCallee⟩], [int32]⟩

private def firstId (fn : CallFrame.Callee) : (site fn).TargetId :=
  ⟨0, by change 0 < 2; decide⟩

private def secondId (fn : CallFrame.Callee) : (site fn).TargetId :=
  ⟨1, by change 1 < 2; decide⟩

private def continuation (fn : CallFrame.Callee) : List (Op (site fn)) :=
  [.numeric (.get ⟨1⟩), .numeric (.bin .i32 .mul), .numeric (.bin .i32 .add)]

private def later (fn : CallFrame.Callee) : List (Op (site fn)) := .call (secondId fn) :: continuation fn

private def code (fn : CallFrame.Callee) : List (Op (site fn)) :=
  [.numeric (.get ⟨0⟩), .call (firstId fn)] ++ later fn

private def store (fn : CallFrame.Callee) : V1.Execution.Store Unit :=
  { funcs := [.wasm fn.type fn.module fn.v1Func, .wasm secondCallee.type secondCallee.module secondCallee.v1Func] }

private theorem registered (fn : CallFrame.Callee) (typed : fn.program.Typed fn)
    (readOnly : OuterCall.Computed.Sequence.Composed.ReadOnly fn.program) : V1Guard (store fn) (site fn) := by
  have casesId (id : (site fn).TargetId) : id = firstId fn ∨ id = secondId fn := by
    have bound : id.val < 2 := id.isLt
    have casesVal : id.val = 0 ∨ id.val = 1 := by omega
    exact casesVal.elim (fun h => .inl (Fin.ext h)) (fun h => .inr (Fin.ext h))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro id
    rcases casesId id with rfl | rfl
    · exact readOnly
    · simp [Site.target, site, secondId, secondCallee, OuterCall.Computed.Sequence.Composed.ReadOnly]
  · intro id
    rcases casesId id with rfl | rfl
    · exact typed
    · rfl
  · intro id
    rcases casesId id with rfl | rfl <;> rfl
  · intro id
    rcases casesId id with rfl | rfl <;> rfl

private theorem firstInvokes (fn : CallFrame.Callee) (count : fn.params.length = 1) :
    Runs (site fn) (.running saved (code fn)) (.active (firstId fn) (.invoke saved [i32 5]) (later fn)) := by
  have load : Edge (site fn) (.running saved (code fn))
      (.running (saved ++ [i32 5]) (.call (firstId fn) :: later fn)) :=
    fact (.numeric (.get rfl))
  exact (Relation.ReflTransGen.single load).tail
    (fact (.resolve (firstId fn) saved [i32 5] (later fn) count.symm))

private theorem firstReturned :
    Runs (site firstCallee) (.running saved (code firstCallee))
      (.running (saved ++ [i32 7]) (later firstCallee)) := by
  have entry := (firstInvokes firstCallee rfl).tail (call (by trivial) (CallFrame.fact (.enter saved [i32 5] rfl)))
  have pop := entry.tail (call (by trivial) (CallFrame.fact (.labelReturn saved [i32 5] [i32 7])))
  exact pop.tail (call (by trivial) (CallFrame.fact (.frameReturn saved [i32 5] [] [i32 7] rfl)))

private theorem secondInvokes :
    Runs (site firstCallee) (.running saved (code firstCallee))
      (.active (secondId firstCallee) (.invoke saved [i32 7]) (continuation firstCallee)) :=
  firstReturned.tail (fact (.resolve (secondId firstCallee) saved [i32 7] (continuation firstCallee) rfl))

private theorem normalPath : Runs (site firstCallee) (.running saved (code firstCallee)) (.running [i32 17] []) := by
  have entry := secondInvokes.tail (call (by trivial) (CallFrame.fact (.enter saved [i32 7] rfl)))
  have read := entry.tail (call (by trivial) (CallFrame.reduce saved (Locals.fact (.get [i32 7] ⟨0⟩ (i32 7) rfl))))
  have label := read.tail (call (by trivial) (CallFrame.fact (.labelValues saved [i32 7] [i32 7])))
  have returned := label.tail (call (by trivial) (CallFrame.fact (.frameValues saved [i32 7] [i32 7] rfl)))
  have load := returned.tail (fact (.numeric (.get rfl)))
  have mul : intBinOp .i32 .mul 7 2 = .ok 14 := rfl
  have product := load.tail (fact (.numeric (.bin (stack := saved) mul)))
  have add : intBinOp .i32 .add 3 14 = .ok 17 := rfl
  exact product.tail (fact (.numeric (.bin (stack := []) add)))

private theorem firstTrapped :
    Runs (site trappingCallee) (.running saved (code trappingCallee)) (.trapped saved (later trappingCallee)) := by
  have entry := (firstInvokes trappingCallee rfl).tail (call (by trivial) (CallFrame.fact (.enter saved [i32 5] rfl)))
  have raises := entry.tail (call (by trivial) (CallFrame.fact (.unreachable saved [i32 5])))
  have label := raises.tail (call (by trivial) (CallFrame.fact (.labelTrap saved [i32 5])))
  exact label.tail (call (by trivial) (CallFrame.fact (.frameTrap saved [i32 5])))

private theorem dropSecond : Edge (site trappingCallee) (.trapped saved (later trappingCallee))
    (.trapped saved (continuation trappingCallee)) :=
  fact (.discard (.cut saved [] [Op.call (secondId trappingCallee)] (continuation trappingCallee) (.inr (by simp))))

private theorem trapPath : Runs (site trappingCallee) (.running saved (code trappingCallee)) (.trapped [] []) :=
  (firstTrapped.tail dropSecond).tail
    (fact (.discard (.cut [] saved (continuation trappingCallee) [] (.inl (by simp [saved])))))

example : V1.Execution.Steps CallFrame.v1NoHost (v1Config (store firstCallee) (site firstCallee)
    (.running saved (code firstCallee))) ⟨store firstCallee, caller, [.source (.intConst .i32 17)]⟩ :=
  (v1_run_iff (registered firstCallee rfl trivial) (a := .running saved (code firstCallee)) rfl).mpr
    ⟨_, normalPath, rfl, rfl⟩

example : Lime1.Execution.Steps CallFrame.limeNoHost
    (v1Config (store firstCallee) (site firstCallee) (.running saved (code firstCallee))).toLime
    ⟨(store firstCallee).mapCode V1.Func.toLime, caller, [.source (.intConst .i32 3), .source (.intConst .i32 7),
      .invoke ⟨1⟩, .source (.localGet ⟨1⟩), .source (.intBinOp .i32 .mul), .source (.intBinOp .i32 .add)]⟩ := by
  rw [v1_to_lime]
  have g := guard_to_lime (registered firstCallee rfl trivial)
  exact (lime_run_iff g (a := .running saved (code firstCallee)) rfl).mpr
    ⟨_, secondInvokes, ⟨trivial, ⟨rfl, rfl⟩, rfl⟩, rfl⟩

example : Core.Steps Profile.spec noHost
    (v1Config (store trappingCallee) (site trappingCallee) (.running saved (code trappingCallee))).toLime.toCore
    ⟨((store trappingCallee).mapCode V1.Func.toLime).toCore, caller.toCore, [.trap]⟩ := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g]
  exact (core_run_iff (guard_to_core g) (a := .running saved (code trappingCallee)) rfl).mpr
    ⟨_, trapPath, trivial, rfl⟩

example : Core.Step Profile.spec noHost
    (v1Config (store trappingCallee) (site trappingCallee) (.trapped saved (later trappingCallee))).toLime.toCore
    ⟨((store trappingCallee).mapCode V1.Func.toLime).toCore, caller.toCore,
      [.plain (.intConst .i32 3), .trap, .plain (.localGet ⟨1⟩), .plain (.intBinOp .i32 .mul),
        .plain (.intBinOp .i32 .add)]⟩ := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g]
  exact core_sound (guard_to_core g) dropSecond

example {target : Core.Config Unit}
    (path : Core.Steps Profile.spec noHost
      (v1Config (store trappingCallee) (site trappingCallee) (.trapped saved (later trappingCallee))).toLime.toCore target) :
    ∃ kept rest, target =
      (v1Config (store trappingCallee) (site trappingCallee) (.trapped kept rest)).toLime.toCore := by
  have g := guard_to_lime (registered trappingCallee trivial trivial)
  rw [v1_to_lime, lime_to_core g] at path
  obtain ⟨phase, run, _, eq⟩ := (core_run_iff (guard_to_core g) (a := .trapped saved (later trappingCallee)) trivial).mp path
  obtain ⟨kept, rest, rfl⟩ := trap_bypasses run
  exact ⟨kept, rest, by rw [v1_to_lime, lime_to_core g, eq]⟩

example : ¬ Admitted (site firstCallee) (.running [] [.call (firstId firstCallee)]) := by
  intro ready
  change (none : Option (List NumType)) = some [int32] at ready
  cases ready

end Silmaril.Wasm.Institution.Operational.CallContinuation.StraightLine.Sequence
