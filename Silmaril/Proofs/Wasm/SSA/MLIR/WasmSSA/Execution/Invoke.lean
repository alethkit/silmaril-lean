module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Body
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Determinism
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Execution.Fragment
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Context Expand Ty)
open Silmaril.Wasm.SingleThreaded.Det

variable {H : Type} {P : Profile} {host : HostSemantics H}

private theorem intBody_not_returnCall {a : Admin} (h : a.IsReturnCallRef) : ¬ IntBodyCode [a] := by
  cases a with
  | plain i => cases i <;> simp [IntBodyCode, IntBodyInstr, Admin.IsReturnCallRef, Admin.val?] at *
  | _ => simp_all [IntBodyCode, Admin.IsReturnCallRef, Admin.val?]

private theorem labelExit_intBody {n : Nat} {code out : List Admin}
    (exit : LabelExit n [] code out) (flat : IntBodyCode code) :
    (∃ vs, code = vals vs ∧ out = vals vs) ∨
      (∃ vs rest, code = vals vs ++ .plain .return_ :: rest ∧ out = vals vs ++ [.plain .return_]) := by
  cases exit with
  | vals vs => exact .inl ⟨vs, rfl, rfl⟩
  | ret =>
    rename_i vs rest
    exact .inr ⟨vs, rest, by simp [List.append_assoc], rfl⟩
  | returnCall call =>
    simp only [intBodyCode_append] at flat
    exact (intBody_not_returnCall call flat.1.2).elim
  | _ =>
    try simp only [intBodyCode_append] at flat
    simp [IntBodyCode, IntBodyInstr, Admin.val?] at flat

private theorem frameExit_not_label {s : Store H} {fr : Frame} {n : Nat} {code out body : List Admin}
    (exit : FrameExit s fr n code out) (onlyLabel : code = [.label n [] body]) : False := by
  have split := congrArg fnv onlyLabel
  cases exit with
  | returnCallNull call | returnCallAddr call _ _ _ =>
    simp [List.append_assoc, fnv_cons_of_none (IsReturnCallRef.val_none call),
      fnv_cons_of_none (a := .label n [] body) rfl] at split
  | _ =>
    simp [List.append_assoc, throwing, fnv_cons_of_none (a := .plain .return_) rfl,
      fnv_cons_of_none (a := .plain .throwRef) rfl,
      fnv_cons_of_none (a := .label n [] body) rfl] at split

private def framed (c : Config H) : Config H :=
  ⟨c.store, {}, [.frame 1 c.frame [.label 1 [] c.code]]⟩

private theorem framed_onlyStep {source next target : Config H}
    (flat : IntBodyCode source.code) (running : Step P host source next)
    (step : Step P host (framed source) target) : target = framed next := by
  rcases (Step.frame_inv step) with ⟨_, _, _, inner, rfl⟩ | ⟨_, exit, _⟩
  · rcases (Step.label_inv inner) with ⟨s', f', code', inner', same⟩ | ⟨_, exit, _⟩
    · exact (congrArg (fun c : Config H => (⟨c.store, {}, [.frame 1 c.frame c.code]⟩ : Config H))
        same).trans (congrArg framed (intBody_step_unique flat inner' running))
    · rcases labelExit_intBody exit flat with ⟨vs, code, _⟩ | ⟨vs, rest, code, _⟩
      · rcases source with ⟨s, f, is⟩
        cases code
        exact (Step.not_vals running).elim
      · rcases source with ⟨s, f, is⟩
        cases code
        exact (intBody_return_stuck flat running).elim
  · exact (frameExit_not_label exit rfl).elim

private theorem framed_path {source last finish : Config H} (flat : IntBodyCode source.code)
    (run : Steps P host source last) (leave : DeterministicPath P host (framed last) finish) :
    DeterministicPath P host (framed source) finish := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact leave
  | head step _ ih =>
    obtain ⟨same, nextFlat, _⟩ := intBody_step (Q := P) (host' := host) step flat
    exact .head (.ctxtFrame (.ctxtLabel step)) same (framed_onlyStep flat step) (ih nextFlat)

private theorem label_return_only {s : Store H} {fr : Frame} {w : Val} {target : Config H}
    (step : Step P host ⟨s, fr, [.label 1 [] (vals [w] ++ [.plain .return_])]⟩ target) :
    target = ⟨s, fr, vals [w] ++ [.plain .return_]⟩ := by
  rcases (Step.label_inv step) with ⟨_, _, _, inner, _⟩ | ⟨_, exit, rfl⟩
  · exact (Step.return_vals_stuck inner).elim
  · have flat : IntBodyCode (vals [w] ++ [.plain .return_]) :=
      intBodyCode_append.mpr ⟨intBodyCode_vals _, by simp [IntBodyCode, IntBodyInstr]⟩
    rcases labelExit_intBody exit flat with ⟨vs, code, _⟩ | ⟨vs, rest, code, rfl⟩
    · exact (vals_ne_append_cons rfl code.symm).elim
    · obtain ⟨rfl, _, _⟩ := vals_append_cons_inj code rfl rfl
      rfl

private theorem frame_return_only {s : Store H} {fr : Frame} {w : Val} {target : Config H}
    (step : Step P host ⟨s, {}, [.frame 1 fr (vals [w] ++ [.plain .return_])]⟩ target) :
    target = ⟨s, {}, vals [w]⟩ := by
  rcases (Step.frame_inv step) with ⟨_, _, _, inner, _⟩ | ⟨_, exit, rfl⟩
  · exact (Step.return_vals_stuck inner).elim
  · generalize code : vals [w] ++ [.plain .return_] = is at exit
    have split := congrArg fnv code
    cases exit with
    | ret arity =>
      rename_i before returned rest
      have lists : vals [w] ++ .plain .return_ :: [] =
          vals (before ++ returned) ++ .plain .return_ :: rest := by
        simpa only [vals_append, List.append_assoc, List.singleton_append] using code
      obtain ⟨words, _, _⟩ := vals_append_cons_inj lists rfl rfl
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp arity
      have same : w = v := ((List.append_singleton_inj (as := []) (bs := before)).mp words).2
      subst v
      rfl
    | returnCallNull call | returnCallAddr call _ _ _ =>
      simp [List.append_assoc, fnv_cons_of_none (IsReturnCallRef.val_none call),
        fnv_cons_of_none (a := .plain .return_) rfl] at split
      have impossible := split.2.1.symm ▸ call
      cases impossible
    | _ =>
      simp [throwing, fnv_cons_of_none (a := .plain .return_) rfl,
        fnv_cons_of_none (a := .plain .throwRef) rfl] at split

private theorem leave_frame {s : Store H} {fr : Frame} {w : Val} :
    DeterministicPath P host (framed ⟨s, fr, vals [w] ++ [.plain .return_]⟩) ⟨s, {}, vals [w]⟩ := by
  have label : Step P host (framed ⟨s, fr, vals [w] ++ [.plain .return_]⟩)
      ⟨s, {}, [.frame 1 fr (vals [w] ++ [.plain .return_])]⟩ := by
    apply Step.ctxtFrame
    simpa only [List.append_nil] using
      (Step.returnLabel (P := P) (host := host) (s := s) (f := fr) (n := 1)
        (cont := []) (vs := [w]) (rest := []))
  have frame : Step P host ⟨s, {}, [.frame 1 fr (vals [w] ++ [.plain .return_])]⟩
      ⟨s, {}, vals [w]⟩ := by
    simpa only [vals_nil, List.nil_append, List.append_nil] using
      (Step.returnFrame (P := P) (host := host) (s := s) (f := {}) (fi := fr)
        (n := 1) (vs' := []) (vs := [w]) (rest := []) rfl)
  refine .head label rfl ?_ (.head frame rfl frame_return_only (.refl _))
  intro target step
  rcases (Step.frame_inv step) with ⟨_, _, _, inner, rfl⟩ | ⟨_, exit, _⟩
  · exact congrArg (fun c : Config H => (⟨c.store, {}, [.frame 1 c.frame c.code]⟩ : Config H))
      (label_return_only inner)
  · exact (frameExit_not_label exit rfl).elim

theorem toWasm_invoke_completes {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (P : Profile) (host : HostSemantics H) (s : Store H) (addr : Nat) (fi : FuncInst H)
    (lookup : s.funcs[addr]? = some fi) (code : fi.code = .wasm (f.toWasm C type fits))
    (signature : Expand fi.type (Func.coreSignature params result)) :
    CompletesAt P host (invoke s addr args.toWasmArgs) ⟨s, {}, vals [result.toVal (f.eval args)]⟩ := by
  have arity : args.toWasmArgs.length = (Ty.ofList (Func.paramTypes params)).length := by
    simpa [Ty.length_ofList, Func.paramTypes] using toWasmArgs_length args
  let entry : Config H := ⟨s, Frame.forCall fi.module args.toWasmArgs (f.toWasm C type fits).locals,
    expression (f.toWasm C type fits).body⟩
  let ref := Admin.callRefType ((s.funcs[addr]?.map FuncInst.type).getD default)
  have isCall : ref.IsCallRef := trivial
  have enter : Step P host (invoke s addr args.toWasmArgs) (framed entry) :=
    .callRefFunc isCall lookup signature arity code
  obtain ⟨_, run⟩ := toWasm_returns f C type fits args fi.module P host s
  have rest := framed_path (toWasm_intBody f C type fits) run leave_frame
  have path : DeterministicPath P host (invoke s addr args.toWasmArgs)
      ⟨s, {}, vals [result.toVal (f.eval args)]⟩ :=
    .head enter rfl (Step.callRef_wasm_inv_exact isCall lookup code signature arity) rest
  exact path.completes (fun _ => Step.not_vals)

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA
