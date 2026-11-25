module

import Silmaril.Wasm.Institution.Operational.Loops.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.V1.Validation.Instructions
import Silmaril.Wasm.Versions.Lime1.Execution.Thms

open Silmaril.Wasm
open Silmaril.Wasm.Institution.Operational
open Execution.Runtime (Frame Value)
open SingleThreaded.Det (noHost)

private abbrev zero : LabelIdx := ⟨0⟩
private abbrev int64 := NumType.int .i64
private abbrev saved := [Value.int .i32 9]
private abbrev scratch := [Value.int .i64 42]
private def frame : Frame := ⟨[], {}⟩

private theorem cycleEndpoints {C : Type} {step : C → C → Prop} {a b dst : C}
    (enter : ∀ {next}, step a next ↔ next = b) (restart : ∀ {next}, step b next ↔ next = a) :
    Relation.ReflTransGen step a dst ↔ dst = a ∨ dst = b := by
  constructor
  · intro run
    induction run with
    | refl => exact .inl rfl
    | tail _ edge ih =>
      rcases ih with rfl | rfl
      · exact .inr (enter.mp edge)
      · exact .inl (restart.mp edge)
  · rintro (rfl | rfl)
    · exact .refl
    · exact .single (enter.mpr rfl)


section Core

open Execution.Core

private def coreStore : Store Unit := {}
private def coreEntry : Admin := .plain (.loop (Blocks.coreType (some int64)) [.br zero])
private def coreLoop : Config Unit :=
  ⟨coreStore, frame.toCore, vals (saved.map Value.toCore) ++ [coreEntry, .plain .nop]⟩
private def coreEntered : Config Unit :=
  ⟨coreStore, frame.toCore, vals (saved.map Value.toCore) ++ [.label 0 [.loop (Blocks.coreType (some int64)) [.br zero]]
    [.plain (.br zero)], .plain .nop]⟩

example {dst : Config Unit} :
    Relation.ReflTransGen (Step Numerics.Profile.spec noHost) coreLoop dst ↔ dst = coreLoop ∨ dst = coreEntered :=
  cycleEndpoints (Loops.core_entry_iff (result := some int64) (saved := saved.map Value.toCore)
    (body := [.br zero]) (rest := [.plain .nop]))
    (Loops.core_restart_iff (cont := [.loop (Blocks.coreType (some int64)) [.br zero]]) (saved := saved.map Value.toCore)
      (scratch := []) (pending := []) (rest := [.plain .nop]))

-- Restart drops the inner operand and the pending trap. The outer nop remains pending.
example {dst : Config Unit} :
    Step Numerics.Profile.spec noHost
      ⟨coreStore, frame.toCore, vals (saved.map Value.toCore) ++ [.label 0 [.loop (Blocks.coreType (some int64)) [.br zero]]
        (vals (scratch.map Value.toCore) ++ [.plain (.br zero), .trap]), .plain .nop]⟩ dst ↔ dst = coreLoop :=
  Loops.core_restart_iff (saved := saved.map Value.toCore) (scratch := scratch.map Value.toCore)
    (pending := [.trap]) (rest := [.plain .nop])

-- Fallthrough delivers one value even though the restart arity is zero.
example {dst : Config Unit} :
    Step Numerics.Profile.spec noHost
      ⟨coreStore, frame.toCore, vals (saved.map Value.toCore) ++ [.label 0 [.loop (Blocks.coreType (some int64)) [.br zero]]
        (vals (scratch.map Value.toCore)), .plain .nop]⟩ dst ↔
      dst = ⟨coreStore, frame.toCore, vals (saved.map Value.toCore) ++ vals (scratch.map Value.toCore) ++ [.plain .nop]⟩ :=
  Loops.core_result_iff (r := .values scratch) (saved := saved.map Value.toCore)
    (rest := [.plain .nop])

end Core

section Lime

open Lime1.Execution

private def limeStore : Store Unit := {}
private def limeEntry : Admin := .source (.loop (Blocks.limeType (some int64)) [.br zero])
private def limeLoop : Config Unit :=
  ⟨limeStore, frame, values saved ++ [limeEntry, .source .nop]⟩
private def limeEntered : Config Unit :=
  ⟨limeStore, frame, values saved ++ [.label 0 [.loop (Blocks.limeType (some int64)) [.br zero]]
    [.source (.br zero)], .source .nop]⟩

example {dst : Config Unit} :
    Relation.ReflTransGen (Step CallFrame.limeNoHost) limeLoop dst ↔ dst = limeLoop ∨ dst = limeEntered :=
  cycleEndpoints (Loops.lime_entry_iff (result := some int64) (saved := saved)
    (body := [.br zero]) (rest := [.source .nop]))
    (Loops.lime_restart_iff (cont := [.loop (Blocks.limeType (some int64)) [.br zero]]) (saved := saved)
      (scratch := []) (pending := []) (rest := [.source .nop]))

-- Restart drops the inner operand and the pending trap. The outer nop remains pending.
example {dst : Config Unit} :
    Step CallFrame.limeNoHost
      ⟨limeStore, frame, values saved ++ [.label 0 [.loop (Blocks.limeType (some int64)) [.br zero]]
        (values scratch ++ [.source (.br zero), .trap]), .source .nop]⟩ dst ↔ dst = limeLoop :=
  Loops.lime_restart_iff (saved := saved) (scratch := scratch)
    (pending := [.trap]) (rest := [.source .nop])

-- Fallthrough delivers one value even though the restart arity is zero.
example {dst : Config Unit} :
    Step CallFrame.limeNoHost
      ⟨limeStore, frame, values saved ++ [.label 0 [.loop (Blocks.limeType (some int64)) [.br zero]]
        (values scratch), .source .nop]⟩ dst ↔
      dst = ⟨limeStore, frame, values saved ++ values scratch ++ [.source .nop]⟩ :=
  Loops.lime_result_iff (r := .values scratch) (saved := saved)
    (rest := [.source .nop])

end Lime

section V1

open V1.Execution

private def v1Store : Store Unit := {}
private def v1Entry : Admin := .source (.loop (some int64) [.br zero])
private def v1Loop : Config Unit :=
  ⟨v1Store, frame, values saved ++ [v1Entry, .source .nop]⟩
private def v1Entered : Config Unit :=
  ⟨v1Store, frame, values saved ++ [.label 0 [.loop (some int64) [.br zero]]
    [.source (.br zero)], .source .nop]⟩

example {dst : Config Unit} :
    Relation.ReflTransGen (Step CallFrame.v1NoHost) v1Loop dst ↔ dst = v1Loop ∨ dst = v1Entered :=
  cycleEndpoints (Loops.v1_entry_iff (result := some int64) (saved := saved)
    (body := [.br zero]) (rest := [.source .nop]))
    (Loops.v1_restart_iff (cont := [.loop (some int64) [.br zero]]) (saved := saved)
      (scratch := []) (pending := []) (rest := [.source .nop]))

-- Restart drops the inner operand and the pending trap. The outer nop remains pending.
example {dst : Config Unit} :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, values saved ++ [.label 0 [.loop (some int64) [.br zero]]
        (values scratch ++ [.source (.br zero), .trap]), .source .nop]⟩ dst ↔ dst = v1Loop :=
  Loops.v1_restart_iff (saved := saved) (scratch := scratch)
    (pending := [.trap]) (rest := [.source .nop])

-- Fallthrough delivers one value even though the restart arity is zero.
example {dst : Config Unit} :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, values saved ++ [.label 0 [.loop (some int64) [.br zero]]
        (values scratch), .source .nop]⟩ dst ↔
      dst = ⟨v1Store, frame, values saved ++ values scratch ++ [.source .nop]⟩ :=
  Loops.v1_result_iff (r := .values scratch) (saved := saved)
    (rest := [.source .nop])

-- The loop's restart code is skipped on trap and explicit return alike.
example {dst : Config Unit} :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, values saved ++ [.label 0 [.loop (some int64) [.br zero]] [.trap], .source .nop]⟩
      dst ↔ dst = ⟨v1Store, frame, values saved ++ [.trap, .source .nop]⟩ :=
  Loops.v1_result_iff (saved := saved) (r := .trap) (rest := [.source .nop])

example :
    Step CallFrame.v1NoHost
      ⟨v1Store, frame, values saved ++ [.label 0 [.loop (some int64) [.br zero]]
        (values scratch ++ [.source .return_, .trap]), .source .nop]⟩
      ⟨v1Store, frame, values (saved ++ scratch) ++ [.source .return_, .source .nop]⟩ :=
  Step.context
    (Step.pure _ _ (PureStep.labelReturn 0 [.loop (some int64) [.br zero]] scratch [.trap]))
    saved [.source .nop]

end V1

example (C : V1.Validation.Context) :
    V1.Validation.InstrType C (.loop (some int64) [.br zero]) [] [int64] :=
  .loop (some int64) (.singleton (.br zero rfl [] [int64]))

section FiniteIteration

open V1.Execution

private abbrev flag : LocalIdx := ⟨0⟩
private abbrev one := Value.int .i32 1
private abbrev off := Value.int .i32 0

private def onceBody : V1.Expr :=
  [.localGet flag, .intConst .i32 0, .localSet flag, .brIf zero, .intConst .i64 42]

example :
    V1.Validation.InstrType { locals := [.i32] } (.loop (some int64) onceBody) [] [int64] := by
  apply V1.Validation.InstrType.loop
  refine .cons (.localGet flag rfl) ?_
  refine .cons (.frame [.i32] (.intConst .i32 0)) ?_
  refine .cons (.frame [.i32] (.localSet flag rfl)) ?_
  exact .cons (.brIf (ts := []) zero rfl) (.singleton (.intConst .i64 42))

private def onceLoop : V1.Instr := .loop (some int64) onceBody
private def onceTail : List Admin := [.source (.localGet flag)]
private def onceCode : List Admin := values saved ++ .source onceLoop :: onceTail
private def onceFrame (v : Value) : Frame := ⟨[v], {}⟩

private def onceConfig (f : Frame) (code : List Admin) : Config Unit := ⟨v1Store, f, code⟩

private def inIteration (code : List Admin) : List Admin :=
  values saved ++ .label 0 [onceLoop] code :: onceTail

private theorem iterationStep {f f' : Frame} {a b : List Admin}
    (edge : Step CallFrame.v1NoHost (onceConfig f a) (onceConfig f' b)) :
    Step CallFrame.v1NoHost (onceConfig f (inIteration a)) (onceConfig f' (inIteration b)) :=
  (Blocks.Context.v1_label_cont_iff (cont := [onceLoop]) (saved := saved) (rest := onceTail)).mpr
    (.inl ⟨_, edge, rfl⟩)

private theorem iterationTest (v : Value) :
    Relation.ReflTransGen (Step CallFrame.v1NoHost) (onceConfig (onceFrame v) onceCode)
      (onceConfig (onceFrame off) (inIteration (value v :: expression [.brIf zero, .intConst .i64 42]))) := by
  have enter : Step CallFrame.v1NoHost (onceConfig (onceFrame v) onceCode)
      (onceConfig (onceFrame v) (inIteration (expression onceBody))) :=
    (Loops.v1_entry_iff (result := some int64) (saved := saved) (body := onceBody) (rest := onceTail)).mpr rfl
  have get : Step CallFrame.v1NoHost (onceConfig (onceFrame v) (expression onceBody))
      (onceConfig (onceFrame v) (value v :: expression onceBody.tail)) :=
    Step.context (Step.localGet _ _ flag v rfl) [] (expression onceBody.tail)
  have set : Step CallFrame.v1NoHost
      (onceConfig (onceFrame v) (value v :: expression onceBody.tail))
      (onceConfig (onceFrame off) (value v :: expression [.brIf zero, .intConst .i64 42])) :=
    Step.context (Step.localSet _ _ flag off v rfl) [v] (expression [.brIf zero, .intConst .i64 42])
  exact ((Relation.ReflTransGen.single enter).tail (iterationStep get)).tail (iterationStep set)

private def onceStart := onceConfig (onceFrame one) onceCode
private def onceEnd := onceConfig (onceFrame off) (values (saved ++ scratch ++ [off]))

private theorem executesOnce : Relation.ReflTransGen (Step CallFrame.v1NoHost) onceStart onceEnd := by
  have taken := Step.context (Step.pure (host := CallFrame.v1NoHost) v1Store (onceFrame off)
    (PureStep.brIfNonzero zero 1 (by decide))) [] (expression [.intConst .i64 42])
  have skipped := Step.context (Step.pure (host := CallFrame.v1NoHost) v1Store (onceFrame off)
    (PureStep.brIfZero zero)) [] (expression [.intConst .i64 42])
  have restart := (Loops.v1_restart_iff (s := v1Store) (f := onceFrame off)
    (cont := [onceLoop]) (saved := saved) (scratch := []) (pending := expression [.intConst .i64 42])
    (rest := onceTail)).mpr rfl
  have leave := (Loops.v1_result_iff (s := v1Store) (f := onceFrame off)
    (cont := [onceLoop]) (r := .values scratch) (saved := saved) (rest := onceTail)).mpr rfl
  have resume := Step.context (Step.localGet (host := CallFrame.v1NoHost) v1Store (onceFrame off)
    flag off rfl) (saved ++ scratch) []
  have first := ((iterationTest one).tail (iterationStep taken)).tail restart
  have second := (((iterationTest off).tail (iterationStep skipped)).tail leave).tail resume
  exact first.trans second

example : Relation.ReflTransGen (Step CallFrame.v1NoHost) onceStart onceEnd := executesOnce

example : Relation.ReflTransGen (Lime1.Execution.Step CallFrame.limeNoHost) onceStart.toLime onceEnd.toLime := by
  have transport {a b : Config Unit} (run : Relation.ReflTransGen (Step CallFrame.v1NoHost) a b) :
      Relation.ReflTransGen (Lime1.Execution.Step CallFrame.limeNoHost) a.toLime b.toLime := by
    induction run with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail (edge.toLime (fun _ _ _ _ h => h))
  exact transport executesOnce

end FiniteIteration

section CoreFiniteIteration

open Execution.Core

private def coreOnceBody : List Instr :=
  [.localGet flag, .intConst .i32 0, .localSet flag, .brIf zero, .intConst .i64 42]

private def coreOnceLoop : Instr := .loop (Blocks.coreType (some int64)) coreOnceBody
private def coreOnceTail : List Admin := [.plain (.localGet flag)]
private def coreOnceCode : List Admin := Blocks.Context.coreValues saved ++ .plain coreOnceLoop :: coreOnceTail

private def coreOnceConfig (v : Value) (code : List Admin) : Config Unit :=
  ⟨coreStore, (onceFrame v).toCore, code⟩

private def coreInIteration (code : List Admin) : List Admin :=
  Blocks.Context.coreValues saved ++ .label 0 [coreOnceLoop] code :: coreOnceTail

private theorem coreIterationStep {v v' : Value} {a b : List Admin}
    (edge : Step Numerics.Profile.spec noHost (coreOnceConfig v a) (coreOnceConfig v' b)) :
    Step Numerics.Profile.spec noHost (coreOnceConfig v (coreInIteration a))
      (coreOnceConfig v' (coreInIteration b)) :=
  (Blocks.Context.core_label_cont_iff (cont := [coreOnceLoop]) (saved := saved.map Value.toCore)
    (rest := coreOnceTail)).mpr (.inl ⟨_, edge, rfl⟩)

private theorem coreIterationTest (v : Value) :
    Steps Numerics.Profile.spec noHost (coreOnceConfig v coreOnceCode)
      (coreOnceConfig off (coreInIteration (v.toCore.toAdmin :: expression [.brIf zero, .intConst .i64 42]))) := by
  have enter : Step Numerics.Profile.spec noHost (coreOnceConfig v coreOnceCode)
      (coreOnceConfig v (coreInIteration (expression coreOnceBody))) :=
    (Loops.core_entry_iff (result := some int64) (saved := saved.map Value.toCore)
      (body := coreOnceBody) (rest := coreOnceTail)).mpr rfl
  have get : Step Numerics.Profile.spec noHost (coreOnceConfig v (expression coreOnceBody))
      (coreOnceConfig v (v.toCore.toAdmin :: expression coreOnceBody.tail)) :=
    Sim.Step.append_right (.variable (.localGet (x := flag) rfl)) (expression coreOnceBody.tail)
  have set : Step Numerics.Profile.spec noHost
      (coreOnceConfig v (v.toCore.toAdmin :: expression coreOnceBody.tail))
      (coreOnceConfig off (v.toCore.toAdmin :: expression [.brIf zero, .intConst .i64 42])) :=
    Sim.Step.vals_left (Sim.Step.append_right (.variable (.localSet (s := coreStore) (f := (onceFrame v).toCore) (x := flag) (v := off.toCore)
      (show 0 < 1 by decide))) (expression [.brIf zero, .intConst .i64 42])) [v.toCore]
  exact ((Relation.ReflTransGen.single enter).tail (coreIterationStep get)).tail (coreIterationStep set)

example : Steps Numerics.Profile.spec noHost (coreOnceConfig one coreOnceCode)
    (coreOnceConfig off (Blocks.Context.coreValues (saved ++ scratch ++ [off]))) := by
  have taken := Sim.Step.append_right (Step.brIfTrue (P := Numerics.Profile.spec) (host := noHost)
    (s := coreStore) (f := (onceFrame off).toCore) (l := zero) (c := 1) (by decide)) (expression [.intConst .i64 42])
  have skipped := Sim.Step.append_right (Step.brIfFalse (P := Numerics.Profile.spec) (host := noHost)
    (s := coreStore) (f := (onceFrame off).toCore) (l := zero)) (expression [.intConst .i64 42])
  have restart := (Loops.core_restart_iff (P := Numerics.Profile.spec) (s := coreStore)
    (f := (onceFrame off).toCore) (cont := [coreOnceLoop]) (saved := saved.map Value.toCore)
    (scratch := []) (pending := expression [.intConst .i64 42]) (rest := coreOnceTail)).mpr rfl
  have leave := (Loops.core_result_iff (P := Numerics.Profile.spec) (s := coreStore)
    (f := (onceFrame off).toCore) (cont := [coreOnceLoop]) (r := .values scratch)
    (saved := saved.map Value.toCore) (rest := coreOnceTail)).mpr rfl
  have resume := Sim.Step.vals_left (Step.variable (P := Numerics.Profile.spec) (host := noHost)
    (.localGet (s := coreStore) (f := (onceFrame off).toCore) (x := flag) (v := off.toCore) rfl))
    ((saved ++ scratch).map Value.toCore)
  have first := ((coreIterationTest one).tail (coreIterationStep taken)).tail restart
  have second := (((coreIterationTest off).tail (coreIterationStep skipped)).tail leave).tail resume
  exact first.trans second

end CoreFiniteIteration
