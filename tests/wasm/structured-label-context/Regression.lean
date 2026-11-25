module

import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Wasm.Execution.Core.Properties
import Silmaril.Wasm.Execution.Core.Sim.Context

open Silmaril.Wasm
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.Blocks.Context
open Execution.Runtime (Frame FuncAddr Value)
open SingleThreaded.Det (noHost)

private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev int32 := NumType.int .i32
private abbrev int64 := NumType.int .i64
private def frame : Frame := ⟨[i32 41], { funcs := [⟨0⟩] }⟩
private def caller : Frame := ⟨[], {}⟩

-- The inner label expects one fallthrough result and the outer label expects none.
-- The enclosing function is allowed to return a different result list.
private def nested {A : Type} (discard : A) (results : List Value) : Returning A :=
  .under ⟨0, [i32 3], []⟩ (.under ⟨1, [i32 4], [discard]⟩ (.pending results [discard]))

private theorem crossesTwo {A : Type} (discard : A) (results : List Value) :
    ReturnRuns (nested discard results) (.pending ([i32 3, i32 4] ++ results) []) :=
  (Relation.ReflTransGen.single (.under _ (.exit _ results [discard]))).tail
    (.exit _ ([i32 4] ++ results) [discard])

private def pair : List Value := [i64 11, i32 7]

example : (nested (A := Unit) () pair).Typed [int64, int32] := rfl

example : (Returning.pending ([i32 3, i32 4] ++ pair) ([] : List Unit)).Typed [int64, int32] :=
  return_typed_run (a := nested () pair) rfl (crossesTwo () pair)

example : ¬ (nested (A := Unit) () pair).Typed [int32, int64] := by
  change ¬ [int32, int64] = [int64, int32]
  decide

section Core
open Execution.Core

private def coreStore : Store Unit := {}
private def discardCore : Admin := .plain .unreachable
private def coreReturn : Returning Admin := nested discardCore pair

private def coreInner : List Instr := [.intConst .i64 11, .intConst .i32 7, .return_, .unreachable]
private def coreOuter : List Instr := [.intConst .i32 4, .block (Blocks.coreType (some int32)) coreInner, .unreachable]
private def coreSource : List Admin := coreValues [i32 3] ++ [.plain (.block (Blocks.coreType none) coreOuter)]

private theorem coreEnters :
    Steps Numerics.Profile.spec noHost ⟨coreStore, frame.toCore, coreSource⟩ ⟨coreStore, frame.toCore, coreCode coreReturn⟩ := by
  have outer := (Blocks.core_entry_iff (P := Numerics.Profile.spec) (s := coreStore) (f := frame.toCore)
    (result := none) (body := coreOuter)).mpr rfl
  have inner := (Blocks.core_entry_iff (P := Numerics.Profile.spec) (s := coreStore) (f := frame.toCore)
    (result := some int32) (body := coreInner)).mpr rfl
  have first := Sim.Step.vals_left outer ([i32 3].map Value.toCore)
  have inside := Sim.Step.vals_left (Sim.Step.append_right inner [discardCore]) ([i32 4].map Value.toCore)
  have second := (core_label_iff (n := 0) (saved := [i32 3].map Value.toCore) (rest := [])).mpr
    (.inl ⟨_, inside, rfl⟩)
  exact (Relation.ReflTransGen.single first).tail second

example {dst : Config Unit}
    (run : Steps Numerics.Profile.spec noHost ⟨coreStore, frame.toCore, coreCode coreReturn⟩ dst) :
    ∃ out, ReturnRuns coreReturn out ∧ out.Typed [int64, int32] ∧ dst = ⟨coreStore, frame.toCore, coreCode out⟩ := by
  obtain ⟨out, trace, rfl⟩ := (core_return_run_iff coreReturn).mp run
  have typed : coreReturn.Typed [int64, int32] := rfl
  exact ⟨out, trace, return_typed_run typed trace, rfl⟩

example : Steps Numerics.Profile.spec noHost
    ⟨coreStore, caller.toCore, [.frame 2 frame.toCore coreSource]⟩
    ⟨coreStore, caller.toCore, [.plain (.intConst .i64 11), .plain (.intConst .i32 7)]⟩ := by
  have trace := (core_return_run_iff (P := Numerics.Profile.spec) (s := coreStore) (f := frame.toCore) coreReturn).mpr
    ⟨_, crossesTwo discardCore pair, rfl⟩
  exact (Execution.Core.Steps.frame (f := caller.toCore) (n := 2) (coreEnters.trans trace)).tail
    ((CallFrame.core_return_frame_iff (extra := [i32 3, i32 4].map Value.toCore)
      (results := pair.map Value.toCore) rfl).mpr rfl)

example {dst : Config Unit} :
    Step Numerics.Profile.spec noHost
      ⟨coreStore, frame.toCore, [.plain (.intConst .i32 9), .label 1 [] [.plain (.intConst .i32 7)], discardCore]⟩ dst ↔
    dst = ⟨coreStore, frame.toCore, [.plain (.intConst .i32 9), .plain (.intConst .i32 7), discardCore]⟩ :=
  core_result_iff (scope := ⟨1, [i32 9], [discardCore]⟩) (r := .values [i32 7])

example {dst : Config Unit} :
    Step Numerics.Profile.spec noHost
      ⟨coreStore, frame.toCore, [.plain (.intConst .i32 9), .label 1 [] [.trap], discardCore]⟩ dst ↔
    dst = ⟨coreStore, frame.toCore, [.plain (.intConst .i32 9), .trap, discardCore]⟩ :=
  core_result_iff (scope := ⟨1, [i32 9], [discardCore]⟩) (r := .trap)

end Core

section Lime1
open Lime1.Execution

private def limeStore : Store Unit := {}
private def discardLime : Admin := .source .unreachable
private def limeReturn : Returning Admin := nested discardLime pair

private def limeInner : List Lime1.Instr := [.intConst .i64 11, .intConst .i32 7, .return_, .unreachable]
private def limeOuter : List Lime1.Instr := [.intConst .i32 4, .block (Blocks.limeType (some int32)) limeInner, .unreachable]
private def limeSource : List Admin := values [i32 3] ++ [.source (.block (Blocks.limeType none) limeOuter)]

private theorem limeEnters :
    Steps CallFrame.limeNoHost ⟨limeStore, frame, limeSource⟩ ⟨limeStore, frame, limeCode limeReturn⟩ := by
  have outer := (Blocks.lime_entry_iff (host := CallFrame.limeNoHost) (s := limeStore) (f := frame)
    (result := none) (body := limeOuter)).mpr rfl
  have inner := (Blocks.lime_entry_iff (host := CallFrame.limeNoHost) (s := limeStore) (f := frame)
    (result := some int32) (body := limeInner)).mpr rfl
  have first := Step.context outer [i32 3] []
  have inside := Step.context inner [i32 4] [discardLime]
  have second := (lime_label_iff (n := 0) (saved := [i32 3]) (rest := [])).mpr (.inl ⟨_, inside, rfl⟩)
  exact (Relation.ReflTransGen.single first).tail second

example : Steps CallFrame.limeNoHost
    ⟨limeStore, caller, [.frame 2 frame limeSource]⟩
    ⟨limeStore, caller, [.source (.intConst .i64 11), .source (.intConst .i32 7)]⟩ := by
  have trace := (lime_return_run_iff (s := limeStore) (f := frame) limeReturn).mpr
    ⟨_, crossesTwo discardLime pair, rfl⟩
  have framed := Relation.ReflTransGen.lift
    (fun c : Config Unit => (⟨c.store, caller, [.frame 2 c.frame c.code]⟩ : Config Unit))
    (fun _ _ move => Step.frame move 2 caller) _ _ (limeEnters.trans trace)
  exact framed.tail ((CallFrame.lime_return_frame_iff (extra := [i32 3, i32 4]) (results := pair) rfl).mpr rfl)

example {dst : Config Unit} :
    Step CallFrame.limeNoHost
      ⟨limeStore, frame, [.source (.intConst .i32 9), .label 1 [] [.source (.intConst .i32 7)], discardLime]⟩ dst ↔
    dst = ⟨limeStore, frame, [.source (.intConst .i32 9), .source (.intConst .i32 7), discardLime]⟩ :=
  lime_result_iff (scope := ⟨1, [i32 9], [discardLime]⟩) (r := .values [i32 7])

example {dst : Config Unit} :
    Step CallFrame.limeNoHost
      ⟨limeStore, frame, [.source (.intConst .i32 9), .label 1 [] [.trap], discardLime]⟩ dst ↔
    dst = ⟨limeStore, frame, [.source (.intConst .i32 9), .trap, discardLime]⟩ :=
  lime_result_iff (scope := ⟨1, [i32 9], [discardLime]⟩) (r := .trap)

end Lime1

section V1
open V1.Execution

private def v1Store : Store Unit := {}
private def discardV1 : Admin := .source .unreachable
private def v1Return : Returning Admin := nested discardV1 [i32 7]

private def v1Inner : List V1.Instr := [.intConst .i32 7, .return_, .unreachable]
private def v1Outer : List V1.Instr := [.intConst .i32 4, .block (some int32) v1Inner, .unreachable]
private def v1Source : List Admin := values [i32 3] ++ [.source (.block none v1Outer)]

private theorem v1Enters :
    Steps CallFrame.v1NoHost ⟨v1Store, frame, v1Source⟩ ⟨v1Store, frame, v1Code v1Return⟩ := by
  have outer := (Blocks.v1_entry_iff (host := CallFrame.v1NoHost) (s := v1Store) (f := frame)
    (result := none) (body := v1Outer)).mpr rfl
  have inner := (Blocks.v1_entry_iff (host := CallFrame.v1NoHost) (s := v1Store) (f := frame)
    (result := some int32) (body := v1Inner)).mpr rfl
  have first := Step.context outer [i32 3] []
  have inside := Step.context inner [i32 4] [discardV1]
  have second := (v1_label_iff (n := 0) (saved := [i32 3]) (rest := [])).mpr (.inl ⟨_, inside, rfl⟩)
  exact (Relation.ReflTransGen.single first).tail second

example : Steps CallFrame.v1NoHost
    ⟨v1Store, caller, [.frame 1 frame v1Source]⟩
    ⟨v1Store, caller, [.source (.intConst .i32 7)]⟩ := by
  have trace := (v1_return_run_iff (s := v1Store) (f := frame) v1Return).mpr
    ⟨_, crossesTwo discardV1 [i32 7], rfl⟩
  have framed := Relation.ReflTransGen.lift
    (fun c : Config Unit => (⟨c.store, caller, [.frame 1 c.frame c.code]⟩ : Config Unit))
    (fun _ _ move => Step.frame move 1 caller) _ _ (v1Enters.trans trace)
  exact framed.tail (.pure v1Store caller (.frameReturn 1 frame [i32 3, i32 4] [i32 7] [] rfl))

example {dst : Config Unit} :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, [.source (.intConst .i32 9), .label 1 [] [.source (.intConst .i32 7)], discardV1]⟩ dst ↔
    dst = ⟨v1Store, frame, [.source (.intConst .i32 9), .source (.intConst .i32 7), discardV1]⟩ :=
  v1_result_iff (scope := ⟨1, [i32 9], [discardV1]⟩) (r := .values [i32 7])

example {dst : Config Unit} :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, [.source (.intConst .i32 9), .label 1 [] [.trap], discardV1]⟩ dst ↔
    dst = ⟨v1Store, frame, [.source (.intConst .i32 9), .trap, discardV1]⟩ :=
  v1_result_iff (scope := ⟨1, [i32 9], [discardV1]⟩) (r := .trap)

end V1

namespace RankedFixture

open CallContinuation.OuterCall (CallTarget)
open CallContinuation.OuterCall.Ranked
open Graph

private def leaf : Function :=
  ⟨⟨{}, ⟨0⟩, [], [], [int32]⟩, 0, [i32 99, i32 7], [.return_, .unreachable]⟩

private def program : Program := ⟨[some leaf]⟩
private def target : CallTarget := ⟨⟨0⟩, ⟨0⟩, leaf.declaration⟩
private theorem root : Root program frame target leaf := ⟨rfl, rfl, rfl⟩
private theorem checked : program.check = true := rfl
private theorem checkedV1 : program.checkV1 = true := rfl
private def activation : Phase := .returning [] [i32 99, i32 7]
private theorem admitted : Admitted program leaf activation := .returning rfl rfl

private theorem lookup {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn) :
    address = target.address ∧ fn = leaf := by
  rcases address with ⟨n⟩
  cases n with
  | zero =>
    have same : some leaf = some fn := found
    exact ⟨rfl, (Option.some.inj same).symm⟩
  | succ n => simp [Program.lookup, program] at found


open Execution.Core in
private def coreAllocStore : Store Unit := { funcs := [Function.coreInstance leaf] }

private theorem coreAllocated : program.CoreAllocated coreAllocStore := by
  intro address fn found
  obtain ⟨rfl, rfl⟩ := lookup found
  rfl

open Execution.Core in
private theorem coreRankedInBlock {dst : Config Unit} :
    let wrap : Config Unit → Config Unit := fun c =>
      ⟨c.store, c.frame, vals ([i32 9].map Value.toCore) ++ .label 1 [] c.code :: [.plain .unreachable]⟩
    Step Numerics.Profile.spec noHost (wrap (Graph.coreConfig coreAllocStore frame target activation)) dst ↔
      ∃ out, program.Edge checked target.address activation out ∧
        dst = wrap (Graph.coreConfig coreAllocStore frame target out) := by
  intro wrap
  have inner {mid : Config Unit} := Graph.core_step_iff (P := Numerics.Profile.spec) checked coreAllocated root (b := mid) admitted
  change Step Numerics.Profile.spec noHost (wrap (Graph.coreConfig coreAllocStore frame target activation)) dst ↔ _
  have context :
      Step Numerics.Profile.spec noHost (wrap (Graph.coreConfig coreAllocStore frame target activation)) dst ↔
        ∃ mid, Step Numerics.Profile.spec noHost (Graph.coreConfig coreAllocStore frame target activation) mid ∧ dst = wrap mid :=
    core_frame_iff
  rw [context]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, edge, rfl⟩ := inner.mp move
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact ⟨_, inner.mpr ⟨out, edge, rfl⟩, rfl⟩

open Execution.Core in
example : Steps Numerics.Profile.spec noHost
    ⟨coreAllocStore, frame.toCore, [.plain (.intConst .i32 9),
      .label 1 [] (Graph.coreConfig coreAllocStore frame target activation).code, discardCore]⟩
    ⟨coreAllocStore, frame.toCore, [.plain (.intConst .i32 9), .plain (.intConst .i32 7), discardCore]⟩ := by
  have returns := (program.edge_iff checked root.found).mpr (.returnFrame [] [i32 99] [i32 7] rfl)
  have inner := coreRankedInBlock.mpr ⟨_, returns, rfl⟩
  exact (Relation.ReflTransGen.single inner).tail
    ((core_result_iff (scope := ⟨1, [i32 9], [discardCore]⟩) (r := .values [i32 7])).mpr rfl)


open Lime1.Execution in
private def limeAllocStore : Store Unit := { funcs := [.wasm leaf.declaration.type leaf.declaration.module leaf.limeFunc] }

private theorem limeAllocated : program.LimeAllocated limeAllocStore := by
  intro address fn found
  obtain ⟨rfl, rfl⟩ := lookup found
  rfl

open Lime1.Execution in
example {dst : Config Unit} :
    let wrap : Config Unit → Config Unit := fun c =>
      ⟨c.store, c.frame, values ([i32 9]) ++ .label 1 [] c.code :: [.source .unreachable]⟩
    Step CallFrame.limeNoHost (wrap (Graph.limeConfig limeAllocStore frame target activation)) dst ↔
      ∃ out, program.Edge checked target.address activation out ∧
        dst = wrap (Graph.limeConfig limeAllocStore frame target out) := by
  intro wrap
  have inner {mid : Config Unit} := Graph.lime_step_iff checked limeAllocated root (b := mid) admitted
  change Step CallFrame.limeNoHost (wrap (Graph.limeConfig limeAllocStore frame target activation)) dst ↔ _
  have context :
      Step CallFrame.limeNoHost (wrap (Graph.limeConfig limeAllocStore frame target activation)) dst ↔
        ∃ mid, Step CallFrame.limeNoHost (Graph.limeConfig limeAllocStore frame target activation) mid ∧ dst = wrap mid :=
    lime_frame_iff
  rw [context]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, edge, rfl⟩ := inner.mp move
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact ⟨_, inner.mpr ⟨out, edge, rfl⟩, rfl⟩

open V1.Execution in
private def v1AllocStore : Store Unit := { funcs := [.wasm leaf.declaration.type leaf.declaration.module leaf.v1Func] }

private theorem v1Allocated : program.V1Allocated v1AllocStore := by
  intro address fn found
  obtain ⟨rfl, rfl⟩ := lookup found
  rfl

open V1.Execution in
example {dst : Config Unit} :
    let wrap : Config Unit → Config Unit := fun c =>
      ⟨c.store, c.frame, values ([i32 9]) ++ .label 1 [] c.code :: [.source .unreachable]⟩
    Step CallFrame.v1NoHost (wrap (Graph.v1Config v1AllocStore frame target activation)) dst ↔
      ∃ out, program.Edge (Bool.and_eq_true_iff.mp checkedV1).1 target.address activation out ∧
        dst = wrap (Graph.v1Config v1AllocStore frame target out) := by
  intro wrap
  have inner {mid : Config Unit} := Graph.v1_step_iff checkedV1 v1Allocated root (b := mid) admitted rfl
  change Step CallFrame.v1NoHost (wrap (Graph.v1Config v1AllocStore frame target activation)) dst ↔ _
  have context :
      Step CallFrame.v1NoHost (wrap (Graph.v1Config v1AllocStore frame target activation)) dst ↔
        ∃ mid, Step CallFrame.v1NoHost (Graph.v1Config v1AllocStore frame target activation) mid ∧ dst = wrap mid :=
    v1_frame_iff
  rw [context]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, edge, rfl⟩ := inner.mp move
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact ⟨_, inner.mpr ⟨out, edge, rfl⟩, rfl⟩

end RankedFixture
