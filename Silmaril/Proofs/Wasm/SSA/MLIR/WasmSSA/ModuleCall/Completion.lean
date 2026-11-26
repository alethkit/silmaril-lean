module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Wasm.Abstract.HostCall.Thms
import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Thms

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall

open Silmaril.MLIR.WasmSSA
open Silmaril.Wasm (Func FuncIdx LocalIdx)
open Silmaril.Wasm.Abstract (frameExit_label labelExit_stuck)
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded.Det (fnv fnv_cons_of_none vals_nil)
open Silmaril.Wasm.Validation (Expand Ty)

variable {H : Type} {P : Profile} {host : HostSemantics H}

theorem completes_here {c : Config H} (stopped : ∀ other, ¬ Step P host c other) :
    CompletesAt P host c c := by
  have same {other : Config H} (run : Steps P host c other) : other = c := by
    rcases run.cases_head with rfl | ⟨_, step, _⟩
    · rfl
    · exact (stopped _ step).elim
  refine ⟨.refl, fun _ run => same run ▸ .refl, stopped,
    fun _ run => congrArg Config.store (same run), ?_, ?_⟩
  · intro c' _ _ run step _
    exact (stopped _ (same run ▸ step)).elim
  · intro infinite
    obtain ⟨_, step, _⟩ := infinite.unfold
    exact stopped _ step

private theorem completes_prepend {start next finish : Config H}
    (advance : Step P host start next) (same : next.store = start.store)
    (only : ∀ {other}, Step P host start other → other = next)
    (complete : CompletesAt P host next finish) : CompletesAt P host start finish := by
  have split {c : Config H} (run : Steps P host start c) : c = start ∨ Steps P host next c := by
    rcases run.cases_head with rfl | ⟨_, step, tail⟩
    · exact .inl rfl
    · exact .inr (only step ▸ tail)
  refine ⟨.head advance complete.reaches, ?_, complete.stopped, ?_, ?_, ?_⟩
  · intro c run
    rcases split run with rfl | tail
    · exact .head advance complete.reaches
    · exact complete.continues c tail
  · intro c run
    rcases split run with rfl | tail
    · rfl
    · exact (complete.sameStore c tail).trans same
  · intro c _ _ run left right
    rcases split run with rfl | tail
    · exact (only left).trans (only right).symm
    · exact complete.uniqueStep tail left right
  · intro infinite
    obtain ⟨_, step, tail⟩ := infinite.unfold
    exact complete.noDivergence (only step ▸ tail)

private def inSequence (below : List Val) (rest : List Admin) (c : Config H) : Config H :=
  ⟨c.store, c.frame, vals below ++ (c.code ++ rest)⟩

private def inCallFrame (caller : Frame) (arity : Nat) (body : Config H) : Config H :=
  ⟨body.store, caller, [.frame arity body.frame [.label arity [] body.code]]⟩

private theorem frameStep_then {s : Store H} {caller inner : Frame} {arity : Nat}
    {code rest : List Admin} {below : List Val} {next finish : Config H}
    (move : Step P host ⟨s, caller, [.frame arity inner code]⟩ next)
    (same : next.store = s)
    (only : ∀ {other}, Step P host ⟨s, caller, [.frame arity inner code]⟩ other → other = next)
    (then_ : CompletesAt P host (inSequence below rest next) finish) :
    CompletesAt P host ⟨s, caller, vals below ++ .frame arity inner code :: rest⟩ finish := by
  refine completes_prepend (next := inSequence below rest next) ?_ same ?_ then_
  · cases next
    exact Sim.Step.vals_left (Sim.Step.append_right move rest) below
  · intro other step
    obtain ⟨mid, innerStep, rfl⟩ := Step.ctx_in_seq (X := .frame arity inner code) trivial step
    simpa only [inSequence, List.append_assoc] using congrArg (inSequence below rest) (only innerStep)

private theorem bodyStep_only {caller : Frame} {arity : Nat} {body next other : Config H}
    (move : Step P host body next)
    (only : ∀ {target}, Step P host body target → target = next)
    (step : Step P host (inCallFrame caller arity body) other) :
    other = inCallFrame caller arity next := by
  rcases body with ⟨s, inner, code⟩
  rcases Step.frame_inv step with ⟨_, _, _, labelStep, rfl⟩ | ⟨_, exit, _⟩
  · rcases Step.label_inv labelStep with ⟨_, _, _, inside, same⟩ | ⟨_, exit, _⟩
    · exact (congrArg (fun c : Config H =>
        (⟨c.store, caller, [.frame arity c.frame c.code]⟩ : Config H)) same).trans
          (congrArg (inCallFrame caller arity) (only inside))
    · exact (labelExit_stuck exit next move).elim
  · exact (frameExit_label exit rfl).elim

private theorem returnLabel_only {s : Store H} {caller inner : Frame} {arity : Nat}
    {results : List Val} {target : Config H}
    (step : Step P host
      (inCallFrame caller arity ⟨s, inner, vals results ++ [.plain .return_]⟩) target) :
    target = ⟨s, caller, [.frame arity inner (vals results ++ [.plain .return_])]⟩ := by
  rcases Step.frame_inv step with ⟨_, _, _, labelStep, rfl⟩ | ⟨_, exit, _⟩
  · rcases Step.label_inv labelStep with ⟨_, _, _, inside, _⟩ | ⟨_, exit, same⟩
    · exact (Step.return_vals_stuck inside).elim
    · obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj same
      generalize shape : vals results ++ [.plain .return_] = code at exit
      have split := congrArg fnv shape
      cases exit with
      | vals => rfl
      | ret =>
        simp at split
        obtain ⟨rfl, rfl⟩ := split
        simp
      | brZero => simp [List.append_assoc] at split
      | returnCall call =>
        simp [fnv_cons_of_none (Admin.val?_of_isReturnCallRef call)] at split
        have blocked := split.2.1.symm ▸ call
        exact blocked.elim
      | _ => simp at split
  · exact (frameExit_label exit rfl).elim

private theorem returnFrame_only {s : Store H} {caller inner : Frame} {arity : Nat}
    {results : List Val} {target : Config H} (length : results.length = arity)
    (step : Step P host
      ⟨s, caller, [.frame arity inner (vals results ++ [.plain .return_])]⟩ target) :
    target = ⟨s, caller, vals results⟩ := by
  rcases Step.frame_inv step with ⟨_, _, _, inside, _⟩ | ⟨_, exit, rfl⟩
  · exact (Step.return_vals_stuck inside).elim
  · generalize shape : vals results ++ [.plain .return_] = code at exit
    have split := congrArg fnv shape
    cases exit with
    | ret count =>
      rename_i extra returned rest
      simp [List.append_assoc] at split
      have values : results = returned := List.append_inj_right'
        (show [] ++ results = extra ++ returned from split.1) (length.trans count.symm)
      rw [values]
    | returnCallNull call | returnCallAddr call _ _ _ =>
      simp [List.append_assoc, fnv_cons_of_none (Admin.val?_of_isReturnCallRef call)] at split
      have blocked := split.2.1.symm ▸ call
      exact blocked.elim
    | throw => simp [throwing] at split
    | _ => simp at split

private theorem framed_completes_then {start finish : Config H} {s : Store H} {caller inner : Frame}
    {arity : Nat} {below results : List Val} {rest : List Admin} (length : results.length = arity)
    (body : CompletesAt P host start ⟨s, inner, vals results ++ [.plain .return_]⟩)
    (then_ : CompletesAt P host ⟨s, caller, vals (below ++ results) ++ rest⟩ finish) :
    CompletesAt P host (inSequence below rest (inCallFrame caller arity start)) finish := by
  have leave : CompletesAt P host
      (inSequence below rest (inCallFrame caller arity ⟨s, inner, vals results ++ [.plain .return_]⟩))
      finish := by
    have popLabel : Step P host
        (inCallFrame caller arity ⟨s, inner, vals results ++ [.plain .return_]⟩)
        ⟨s, caller, [.frame arity inner (vals results ++ [.plain .return_])]⟩ := by
      apply Step.ctxtFrame
      simpa only [List.append_nil] using (Step.returnLabel (rest := []))
    have popFrame : Step P host ⟨s, caller, [.frame arity inner (vals results ++ [.plain .return_])]⟩
        ⟨s, caller, vals results⟩ := by
      simpa only [vals_nil, List.nil_append, List.append_nil] using
        (Step.returnFrame (P := P) (host := host) (s := s) (f := caller) (fi := inner)
          (vs' := []) (vs := results) (rest := []) length)
    have resume : CompletesAt P host (inSequence below rest ⟨s, caller, vals results⟩) finish := by
      simpa only [inSequence, vals_append, List.append_assoc] using then_
    exact frameStep_then popLabel rfl (fun step => returnLabel_only step)
      (frameStep_then popFrame rfl (fun step => returnFrame_only length step) resume)
  have lift {current : Config H} (seen : Steps P host start current)
      (run : Steps P host current ⟨s, inner, vals results ++ [.plain .return_]⟩) :
      CompletesAt P host (inSequence below rest (inCallFrame caller arity current)) finish := by
    induction run using Relation.ReflTransGen.head_induction_on with
    | refl => exact leave
    | @head current next move _ ih =>
      have seenNext := seen.tail move
      have same := (body.sameStore _ seenNext).trans (body.sameStore _ seen).symm
      rcases current with ⟨_, _, _⟩
      rcases next with ⟨_, _, _⟩
      exact frameStep_then (.ctxtFrame (.ctxtLabel move)) same
        (bodyStep_only move (fun other => body.uniqueStep seen other move)) (ih seenNext)
  exact lift .refl body.reaches

theorem directCall_completes_then {s : Store H} {caller : Frame} {x : FuncIdx}
    {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)}
    {below args results : List Val} {rest : List Admin} {finish : Config H}
    (index : caller.module.funcs[x.toNat]? = some a) (lookup : s.funcs[a]? = some fi)
    (stored : fi.code = .wasm code) (signature : Expand fi.type (.func ps rs))
    (arity : args.length = ps.length) (resultArity : results.length = rs.length)
    (body : ∃ final, CompletesAt P host
      ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
      ⟨s, final, vals results ++ [.plain .return_]⟩)
    (then_ : CompletesAt P host ⟨s, caller, vals (below ++ results) ++ rest⟩ finish) :
    CompletesAt P host ⟨s, caller, vals (below ++ args) ++ .plain (.call x) :: rest⟩ finish := by
  let entry : Config H := ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
  have resolve : Step P host ⟨s, caller, vals (below ++ args) ++ .plain (.call x) :: rest⟩
      ⟨s, caller, vals (below ++ args) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩ :=
    Sim.Step.vals_left (Sim.Step.append_right (Step.call index lookup) rest) (below ++ args)
  apply completes_prepend resolve rfl
  · intro _ step
    obtain ⟨_, _, hx, hf, rfl⟩ := Step.call_vals_inv_seq step
    obtain rfl := Option.some.inj (hx.symm.trans index)
    obtain rfl := Option.some.inj (hf.symm.trans lookup)
    rfl
  · have enter : Step P host
        ⟨s, caller, vals (below ++ args) ++ .ref (.func a) :: .callRefType fi.type :: rest⟩
        (inSequence below rest (inCallFrame caller rs.length entry)) := by
      have root : Step P host ⟨s, caller, vals args ++ [.ref (.func a), .callRefType fi.type]⟩
          (inCallFrame caller rs.length entry) := .callRefFunc trivial lookup signature arity stored
      simpa only [inSequence, inCallFrame, vals_append, List.append_assoc,
        List.cons_append, List.nil_append] using
        Sim.Step.vals_left (Sim.Step.append_right root rest) below
    apply completes_prepend enter rfl
    · intro _ step
      obtain ⟨saved, supplied, ps', rs', split, expands, count, rfl⟩ :=
        Step.callRef_wasm_inv_seq (r := .callRefType fi.type) trivial lookup stored step
      obtain ⟨rfl, rfl⟩ := Ty.func.inj (Option.some.inj
        ((Expand.iff.mp expands).symm.trans (Expand.iff.mp signature)))
      obtain ⟨rfl, rfl⟩ := List.append_inj' split (arity.trans count.symm)
      rfl
    · obtain ⟨_, run⟩ := body
      exact framed_completes_then resultArity run then_

theorem invoke_completes_of_body {s : Store H} {a : Nat} {fi : FuncInst H} {code : Func}
    {ps rs : Ty (.list .val)} {args results : List Val}
    (lookup : s.funcs[a]? = some fi) (stored : fi.code = .wasm code)
    (signature : Expand fi.type (.func ps rs)) (arity : args.length = ps.length)
    (resultArity : results.length = rs.length)
    (body : ∃ final, CompletesAt P host
      ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
      ⟨s, final, vals results ++ [.plain .return_]⟩) :
    CompletesAt P host (invoke s a args) ⟨s, {}, vals results⟩ := by
  let entry : Config H := ⟨s, Frame.forCall fi.module args code.locals, expression code.body⟩
  have enter : Step P host (invoke s a args) (inCallFrame {} rs.length entry) :=
    .callRefFunc (c := .callRefType _) trivial lookup signature arity stored
  apply completes_prepend enter rfl (Step.callRef_wasm_inv_exact trivial lookup stored signature arity)
  obtain ⟨_, run⟩ := body
  have stopped : CompletesAt P host ⟨s, {}, vals results⟩ ⟨s, {}, vals results⟩ :=
    completes_here (fun _ => Step.not_vals)
  simpa only [inSequence, vals_nil, List.nil_append, List.append_nil] using
    framed_completes_then (below := []) (rest := []) (caller := {}) resultArity run
      (by simpa only [List.nil_append, List.append_nil] using stopped)

theorem localGet_completes_then {s : Store H} {f : Frame} {x : LocalIdx} {v : Val}
    {below : List Val} {rest : List Admin} {finish : Config H} (lookup : f.local? x = some (some v))
    (then_ : CompletesAt P host ⟨s, f, vals (below ++ [v]) ++ rest⟩ finish) :
    CompletesAt P host ⟨s, f, vals below ++ .plain (.localGet x) :: rest⟩ finish := by
  have get : Step P host ⟨s, f, vals below ++ [.plain (.localGet x)]⟩
      ⟨s, f, vals (below ++ [v])⟩ := by
    rw [vals_append]
    exact Sim.Step.vals_left (Step.variable (VariableStep.localGet lookup)) below
  have move : Step P host ⟨s, f, vals below ++ .plain (.localGet x) :: rest⟩
      ⟨s, f, vals (below ++ [v]) ++ rest⟩ := by
    simpa only [List.append_assoc, List.singleton_append] using Sim.Step.append_right get rest
  refine completes_prepend move rfl ?_ then_
  rintro ⟨store, frame, code⟩ step
  rcases Sim.Step.split_head (a := .plain (.localGet x)) rfl step with
    ⟨saved, used, next, rfl, inside, rfl⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
  · have flat : IntBodyCode (vals (saved ++ used) ++ [.plain (.localGet x)]) := by
      intro member mem
      rcases List.mem_append.mp mem with value | inst
      · obtain ⟨word, _, rfl⟩ := List.mem_map.mp value
        exact .inl (by simp)
      · obtain rfl := List.mem_singleton.mp inst
        exact .inr ⟨_, rfl, trivial⟩
    have prefixed : Step P host ⟨s, f, vals (saved ++ used) ++ [.plain (.localGet x)]⟩
        ⟨store, frame, vals saved ++ next⟩ := by
      simpa only [vals_append, List.append_assoc] using Sim.Step.vals_left inside saved
    exact congrArg (fun c : Config H => (⟨c.store, c.frame, c.code ++ rest⟩ : Config H))
      (IntBodyCode.step_unique flat prefixed get)
  · cases bad
  · cases bad

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.ModuleCall
