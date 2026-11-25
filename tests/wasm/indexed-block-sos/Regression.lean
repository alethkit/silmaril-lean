module

import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.V1.ToCore.DefTypes
import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Institution.Operational
open Silmaril.Wasm.Institution.Operational.Blocks.Indexed
open Execution.Runtime (ModuleInst Value)
open SingleThreaded.Det (noHost)

private abbrev t32 := NumType.int .i32
private abbrev t64 := NumType.int .i64
private abbrev i32 := Value.int .i32
private abbrev i64 := Value.int .i64
private abbrev first : LocalIdx := ⟨0⟩
private abbrev second : LocalIdx := ⟨1⟩

private def sig : Lime1.FuncType := ⟨[t64, t32], [t32, t64]⟩
private def branchSig : Lime1.FuncType := ⟨[t64, t32, t64], [t32, t64]⟩
private def moduleInst : ModuleInst := { types := [⟨[], [t32]⟩, sig, branchSig] }
private def site : Site := ⟨⟨moduleInst, ⟨0⟩, [], [t32, t64], [t32]⟩, ⟨1⟩, sig, [i64 99]⟩
private def branchSite : Site := { site with index := ⟨2⟩, signature := branchSig }
private def badIndex : Site := { site with index := ⟨3⟩ }

private def args : List Value := [i64 11, i32 7]
private def locals : List Value := [i32 0, i64 0]
private def result : List Value := [i32 7, i64 11]
private def script : List Locals.Op := [.set first, .set second, .get first, .get second]

example : site.checkSource locals args (.locals script) = true := rfl
example : badIndex.checkSource locals args (.locals script) = false := rfl
example : ({ site with signature := branchSig }).checkSource locals args (.locals script) = false := rfl
example : site.checkSource locals [i32 7, i64 11] (.locals script) = false := rfl
example : site.checkSource locals [i32 7] (.locals script) = false := rfl
example : site.checkSource locals args (.locals []) = false := rfl
example : site.checkSource locals args (.locals [.set second, .set first, .get first, .get second]) = false := rfl
example : site.checkSource locals args .branch = false := rfl

-- The block returns two values on fallthrough, but the enclosing function's
-- explicit return takes only the final i32.
example : site.checkSource locals args .return_ = true := rfl
example : ({ site with declaration := { site.declaration with results := [t64] } }).checkSource
    locals args .return_ = false := rfl

private theorem localRun :
    Locals.Runs ⟨locals, Locals.values args ++ script⟩ ⟨result, Locals.values result⟩ := by
  have setFirst := Locals.context (Locals.fact (.set locals first (i32 7) (by decide)))
    [i64 11] [.set second, .get first, .get second]
  have setSecond := Locals.context (Locals.fact (.set [i32 7, i64 0] second (i64 11) (by decide)))
    [] [.get first, .get second]
  have getFirst := Locals.context (Locals.fact (.get result first (i32 7) rfl)) [] [.get second]
  have getSecond := Locals.context (Locals.fact (.get result second (i64 11) rfl)) [i32 7] []
  exact (((Relation.ReflTransGen.single setFirst).tail setSecond).tail getFirst).tail getSecond

private theorem normalRun : Runs site (.source locals args (.locals script)) (.done result result) := by
  have body : Runs site (.label ⟨locals, Locals.values args ++ script⟩) (.label ⟨result, Locals.values result⟩) :=
    Relation.ReflTransGen.lift State.label (fun _ _ h => .reduce h) _ _ localRun
  exact ((Relation.ReflTransGen.single (.enter locals args (.locals script))).trans body).tail
    (.fallthrough result result)

private theorem branchRun :
    Runs branchSite (.source locals (i64 13 :: result) .branch) (.done locals result) :=
  (Relation.ReflTransGen.single (.enter locals (i64 13 :: result) .branch)).tail
    (.branch locals [i64 13] result rfl)

private theorem returnRun : Runs site (.source locals args .return_) (.pendingReturn locals args) :=
  (Relation.ReflTransGen.single (.enter locals args .return_)).tail (.return_ locals args)

private theorem admissible_end {site : Site} {a b : State} (ready : Admitted site a) (run : Runs site a b) :
    Admitted site b := by
  induction run with
  | refl => exact ready
  | tail _ edge ih => exact closed ih edge

private theorem witnessed {site : Site} {a b : State} (ready : Admitted site a) (run : Runs site a b) :
    Execution.Core.Steps Numerics.Profile.spec noHost (coreConfig ({} : Execution.Core.Store Unit) site a)
        (coreConfig {} site b) ∧
      Lime1.Execution.Steps CallFrame.limeNoHost (limeConfig ({} : Lime1.Execution.Store Unit) site a)
        (limeConfig {} site b) :=
  ⟨(core_run_iff ready).mpr ⟨b, run, admissible_end ready run, rfl⟩,
    (lime_run_iff ready).mpr ⟨b, run, admissible_end ready run, rfl⟩⟩

example := witnessed (check_source_iff.mp rfl) normalRun
example := witnessed (check_source_iff.mp rfl) branchRun
example := witnessed (check_source_iff.mp rfl) returnRun

open Execution.Core in
example {dst : Config Unit} :
    ¬ Step Numerics.Profile.spec noHost (coreConfig {} badIndex (.source locals args (.locals script))) dst := by
  intro step
  change Step _ _ ⟨{}, (⟨locals, moduleInst⟩ : Execution.Runtime.Frame).toCore,
    vals ([(i64 99).toCore, (i64 11).toCore, (i32 7).toCore]) ++
      [.plain (.block (.typeIdx ⟨3⟩) (script.map Locals.coreInstr))]⟩ dst at step
  obtain ⟨_, _, _, _, _, resolved, _, _⟩ := Blocks.core_block_step_iff.mp step
  change moduleInst.toCore.blockType? (.typeIdx ⟨3⟩) = _ at resolved
  rw [core_type_idx] at resolved
  contradiction

open Lime1.Execution in
example {dst : Config Unit} :
    ¬ Step CallFrame.limeNoHost (limeConfig {} badIndex (.source locals args (.locals script))) dst := by
  intro step
  change Step _ ⟨{}, ⟨locals, moduleInst⟩, values [i64 99, i64 11, i32 7] ++
    [.source (.block (.typeIdx ⟨3⟩) (script.map Locals.limeInstr))]⟩ dst at step
  obtain ⟨_, _, _, _, resolved, _, _⟩ := CallContinuation.OuterCall.Computed.lime_block_step_iff.mp step
  contradiction

private def outside : Execution.Runtime.Frame := ⟨[i32 101], {}⟩

section AllocatedCore
open Execution.Core

private def coreFn : Func :=
  ⟨site.declaration.typeIndex, site.declaration.locals.map V1.ValType.toCore,
    [.intConst .i64 99, .intConst .i64 11, .intConst .i32 7, .block (.typeIdx site.index) [.return_], .unreachable]⟩

private def coreTrial : Store Unit :=
  { funcs := [⟨site.declaration.type.toDefType, moduleInst.toCore, .wasm coreFn⟩] }

private def inCoreFunction (c : Config Unit) : Config Unit :=
  ⟨c.store, outside.toCore, [.frame 1 c.frame [.label 1 [] (c.code ++ [.plain .unreachable])]]⟩

example : Steps Numerics.Profile.spec noHost
    ⟨coreTrial, outside.toCore, [.ref (.func 0), .callRefType site.declaration.type.toDefType]⟩
    ⟨coreTrial, outside.toCore, [(.i32 7 : Val).toAdmin]⟩ := by
  have enter : Step Numerics.Profile.spec noHost
      ⟨coreTrial, outside.toCore, [.ref (.func 0), .callRefType site.declaration.type.toDefType]⟩
      (inCoreFunction (coreConfig coreTrial site (.source locals args .return_))) := by
    have entry := Step.callRefFunc (P := Numerics.Profile.spec) (host := noHost) (s := coreTrial)
      (f := outside.toCore) (a := 0) (c := .callRefType site.declaration.type.toDefType)
      (vs := []) (code := coreFn) (fi := ⟨site.declaration.type.toDefType, moduleInst.toCore, .wasm coreFn⟩)
      (by simp [Admin.IsCallRef]) rfl
      (Validation.Expand.iff.mpr (V1.FuncType.toDefType_expand site.declaration.type)) rfl rfl
    exact entry
  have block := (core_run_iff (P := Numerics.Profile.spec) (s := coreTrial)
    (check_source_iff.mp rfl : Admitted site (.source locals args .return_))).mpr
    ⟨_, returnRun, admissible_end (check_source_iff.mp rfl) returnRun, rfl⟩
  have inside := Relation.ReflTransGen.lift inCoreFunction
    (fun _ _ step => Step.ctxtFrame (Step.ctxtLabel (Sim.Step.append_right step [.plain .unreachable]))) _ _ block
  have crossing := (Relation.ReflTransGen.single enter).trans inside
  have leave := Step.ctxtFrame (f := outside.toCore) (n := 1)
    (Step.returnLabel (P := Numerics.Profile.spec) (host := noHost) (s := coreTrial)
      (f := (State.frame site (.pendingReturn locals args)).toCore) (n := 1) (cont := [])
      (vs := (site.saved ++ args).map Value.toCore) (rest := [.plain .unreachable]))
  have deliver := (CallFrame.core_return_frame_iff (P := Numerics.Profile.spec) (s := coreTrial)
    (outer := outside.toCore) (inner := (State.frame site (.pendingReturn locals args)).toCore)
    (extra := [(i64 99).toCore, (i64 11).toCore]) (results := [(i32 7).toCore]) rfl).mpr rfl
  exact (crossing.tail leave).tail deliver

end AllocatedCore

section AllocatedLime1
open Lime1.Execution

private def limeFn : Lime1.Func :=
  ⟨site.declaration.typeIndex, site.declaration.locals,
    [.intConst .i64 99, .intConst .i64 11, .intConst .i32 7, .block (.typeIdx site.index) [.return_], .unreachable]⟩

private def limeTrial : Store Unit :=
  { funcs := [.wasm site.declaration.type moduleInst limeFn] }

private def inLimeFunction (c : Config Unit) : Config Unit :=
  ⟨c.store, outside, [.frame 1 c.frame [.label 1 [] (c.code ++ [.source .unreachable])]]⟩

example : Steps CallFrame.limeNoHost ⟨limeTrial, outside, [.invoke ⟨0⟩]⟩
    ⟨limeTrial, outside, [value (i32 7)]⟩ := by
  have enter : Step CallFrame.limeNoHost ⟨limeTrial, outside, [.invoke ⟨0⟩]⟩
      (inLimeFunction (limeConfig limeTrial site (.source locals args .return_))) :=
    .invokeWasm _ _ ⟨0⟩ site.declaration.type moduleInst limeFn [] rfl rfl
  have block := (lime_run_iff (s := limeTrial)
    (check_source_iff.mp rfl : Admitted site (.source locals args .return_))).mpr
    ⟨_, returnRun, admissible_end (check_source_iff.mp rfl) returnRun, rfl⟩
  have inside := Relation.ReflTransGen.lift inLimeFunction
    (fun _ _ step => Step.frame (Step.label (Step.context step [] [.source .unreachable]) 1 []) 1 outside) _ _ block
  have crossing := (Relation.ReflTransGen.single enter).trans inside
  have leave := Step.frame (Step.pure (host := CallFrame.limeNoHost) limeTrial
    (State.frame site (.pendingReturn locals args)) (.labelReturn 1 [] (site.saved ++ args) [.source .unreachable])) 1 outside
  have deliver := (CallFrame.lime_return_frame_iff (s := limeTrial)
    (outer := outside) (inner := State.frame site (.pendingReturn locals args))
    (extra := [i64 99, i64 11]) (results := [i32 7]) rfl).mpr rfl
  exact (crossing.tail leave).tail deliver

end AllocatedLime1
