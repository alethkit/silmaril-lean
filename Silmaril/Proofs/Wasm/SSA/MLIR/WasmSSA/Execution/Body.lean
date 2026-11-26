module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Determinism
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Fragment
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SingleThreaded.Determinism.Vals

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.MLIR.WasmSSA.Lowering
open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Context)

variable {H : Type} {P : Profile} {host : HostSemantics H}

private theorem lowerOp_intBody {C : Context} {params Γ : List IntType} {t : IntType}
    (paramsAt : Slots C params) (valsAt : Slots C Γ) (rhs : Rhs params Γ t) :
    IntBodyCode (expression (lowerOp paramsAt valsAt rhs).erase) := by
  cases rhs with
  | binary op _ _ => cases op <;>
      simp [lowerOp, thenBody, readPair, frame, numeric, expression, IntBodyCode, IntBodyInstr,
        Admin.val?, Silmaril.Wasm.Validation.Intrinsic.Body.erase,
        Silmaril.Wasm.Validation.Intrinsic.Step.erase, BinOp.toWasm]
  | _ => simp [lowerOp, thenBody, readPair, frame, numeric, expression, IntBodyCode, IntBodyInstr,
        Admin.val?, Silmaril.Wasm.Validation.Intrinsic.Body.erase,
        Silmaril.Wasm.Validation.Intrinsic.Step.erase]

private theorem lowerBlock_intBody {C : Context} {params Γ : List IntType} {result : IntType}
    (b : Block params result Γ) (paramsAt : Slots C params) (valsAt : Slots C Γ)
    (next : Nat) (layout : C.locals.drop next = b.bindingTypes.map IntType.localType)
    (fits : C.locals.length ≤ 2 ^ 32) (returns : C.return_ = some [result.closed]) :
    IntBodyCode (expression (lowerBlock b paramsAt valsAt next layout fits returns).erase) := by
  induction b generalizing next with
  | return_ ref =>
    simp [lowerBlock, thenBody, expression, IntBodyCode, IntBodyInstr,
      Silmaril.Wasm.Validation.Intrinsic.Body.erase, Silmaril.Wasm.Validation.Intrinsic.Step.erase]
  | letOp rhs rest ih =>
    simp only [lowerBlock, thenBody, store, expression, Silmaril.Wasm.Validation.Intrinsic.Body.erase,
      Silmaril.Wasm.Validation.Intrinsic.Step.erase, List.map_append, intBodyCode_append]
    refine ⟨lowerOp_intBody paramsAt valsAt rhs, by simp [IntBodyCode, IntBodyInstr], ?_⟩
    apply ih

theorem toWasm_intBody {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) :
    IntBodyCode (expression (f.toWasm C type fits).body) := by
  apply lowerBlock_intBody

/-- A finite path whose individual steps are forced by the Core relation. -/
inductive DeterministicPath (P : Profile) (host : HostSemantics H) : Config H → Config H → Prop where
  | refl (c : Config H) : DeterministicPath P host c c
  | head {start next finish : Config H} (step : Step P host start next)
      (sameStore : next.store = start.store)
      (unique : ∀ {other}, Step P host start other → other = next)
      (tail : DeterministicPath P host next finish) : DeterministicPath P host start finish

theorem DeterministicPath.steps {start finish : Config H}
    (path : DeterministicPath P host start finish) : Steps P host start finish := by
  induction path with
  | refl => exact .refl
  | head step _ _ _ ih => exact .head step ih

theorem DeterministicPath.completes {start finish : Config H}
    (path : DeterministicPath P host start finish) (stopped : ∀ c, ¬ Step P host finish c) :
    CompletesAt P host start finish := by
  have reaches {c : Config H} (h : Steps P host start c) :
      Steps P host c finish ∧ c.store = start.store ∧
        ∀ {x y}, Step P host c x → Step P host c y → x = y := by
    induction path with
    | refl =>
      rcases h.cases_head with rfl | ⟨_, step, _⟩
      · exact ⟨.refl, rfl, fun step _ => (stopped _ step).elim⟩
      · exact (stopped _ step).elim
    | head step sameStore unique rest ih =>
      rcases h.cases_head with rfl | ⟨_, nextStep, fromNext⟩
      · exact ⟨.head step rest.steps, rfl, fun hx hy => (unique hx).trans (unique hy).symm⟩
      · obtain ⟨run, same, det⟩ := ih stopped (unique nextStep ▸ fromNext)
        exact ⟨run, same.trans sameStore, det⟩
  refine ⟨path.steps, fun _ h => (reaches h).1, stopped, fun _ h => (reaches h).2.1,
    fun h => (reaches h).2.2, ?_⟩
  · clear reaches
    induction path with
    | refl => exact fun inf => let ⟨_, step, _⟩ := inf.unfold; stopped _ step
    | head _ _ unique _ ih =>
      intro inf
      obtain ⟨_, step, tail⟩ := inf.unfold
      exact ih stopped (unique step ▸ tail)

theorem intBody_path {start finish : Config H} (body : IntBodyCode start.code)
    (path : Steps P host start finish) : DeterministicPath P host start finish := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head step _ ih =>
    obtain ⟨same, nextBody, _⟩ := intBody_step (Q := P) (host' := host) step body
    exact .head step same (fun other => intBody_step_unique body other step) (ih nextBody)

theorem toWasm_body_completes {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (m : ModuleInst) (P : Profile) (host : HostSemantics H) (s : Store H) :
    ∃ final, CompletesAt P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s, final, vals [result.toVal (f.eval args)] ++ [.plain .return_]⟩ := by
  obtain ⟨final, run⟩ := toWasm_returns f C type fits args m P host s
  exact ⟨final, (intBody_path (toWasm_intBody f C type fits) run).completes
    (fun _ => Step.return_vals_stuck)⟩

theorem toWasm_return_unique {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (m : ModuleInst) (s s' : Store H) (final : Frame) (stack : List Val) (rest : List Admin)
    (run : Steps P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s', final, vals stack ++ .plain .return_ :: rest⟩) :
    s' = s ∧ stack = [result.toVal (f.eval args)] ∧ rest = [] := by
  obtain ⟨_, only⟩ := toWasm_body_completes f C type fits args m P host s
  obtain ⟨_, flat⟩ := intBody_steps (toWasm_intBody f C type fits) run
  rcases (only.continues _ run).cases_head with eq | ⟨_, step, _⟩
  · obtain ⟨same, _, code⟩ := Config.mk.inj eq
    obtain ⟨words, _, tail⟩ := Silmaril.Wasm.SingleThreaded.Det.vals_append_cons_inj code rfl rfl
    exact ⟨same, words, tail⟩
  · exact (intBody_return_stuck flat step).elim

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA
