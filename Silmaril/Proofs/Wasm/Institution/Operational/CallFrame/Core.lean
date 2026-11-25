module

public import Silmaril.Wasm.Institution.Operational.CallFrame.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallFrame.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallFrame.Sequence

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallFrame.Proofs

open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Runtime (FuncAddr Value)
open Silmaril.Wasm.SingleThreaded.Det

private abbrev cv (vs : List Value) : List Admin := vals (vs.map Value.toCore)

private theorem armed_frame (fn : Callee) (args : List Value) :
    Frame.forCall fn.module.toCore (args.map Value.toCore) fn.coreFunc.locals =
      (fn.frame (fn.init args)).toCore := by
  simp only [Frame.forCall, Callee.coreFunc, Callee.frame, Callee.init, Runtime.Frame.toCore,
    List.map_append, List.map_map]
  congr 2
  change (fn.locals.map Wasm.V1.ValType.toCore).map (fun t =>
    defaultVal? ((liftVal t).substAll (fn.module.toCore.types.map .dt))) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  cases t <;> rfl

@[local simp] private theorem frame_to_core (fn : Callee) (ls : List Value) :
    (fn.frame ls).toCore = ⟨ls.map Locals.coreLocal, fn.module.toCore⟩ := rfl

private theorem decode_numeric {vs : List Val} (h : Locals.coreCodec.Supported (vals vs)) :
    ∃ ws : List Value, ws.map Value.toCore = vs := by
  induction vs with
  | nil => exact ⟨[], rfl⟩
  | cons v vs ih =>
    obtain ⟨head, rest⟩ := Locals.coreCodec.supports_cons.mp h
    cases v with
    | num n =>
      obtain ⟨xs, rfl⟩ := ih rest
      exact ⟨⟨n.type, n.bits⟩ :: xs, rfl⟩
    | vec | ref => contradiction

private theorem cv_encode (vs : List Value) :
    Locals.coreCodec.encode (Locals.values vs) = cv vs := by
  have one (v : Value) : Locals.coreCodec.emit (.value v) = v.toCore.toAdmin := by
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  simp [Locals.Codec.encode, Locals.values, vals, List.map_map, one]

private theorem expression_locals (code : List Locals.Op) :
    expression ((Program.locals code).instructions Locals.coreInstr .return_ .unreachable) =
      Locals.coreCodec.encode code := List.map_map

private theorem expression_ret (vs : List Value) :
    expression ((Program.ret vs).instructions Locals.coreInstr .return_ .unreachable) =
      cv vs ++ [.plain .return_] := by
  simp only [Program.instructions, expression, List.map_append, List.map_cons, List.map_nil]
  rw [List.map_map, ← cv_encode]
  rfl

private theorem signature (fn : Callee) :
    Expand fn.type.toDefType (.func (Ty.ofList (fn.params.map Ty.num))
      (Ty.ofList (fn.result.toList.map Ty.num))) :=
  Expand.iff.mpr (Wasm.V1.FuncType.toDefType_expand _)

theorem core_sound {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {address : FuncAddr} {fn : Callee} (allocated : s.funcs[address.value]? = some fn.coreInstance)
    {a b : State} (edge : Edge fn a b) :
    Step P noHost (coreConfig s caller address fn a) (coreConfig s caller address fn b) := by
  cases invert edge with
  | @reduce saved before after step =>
    have lifted := Locals.core_sound (P := P) (s := s) (m := fn.module.toCore) step
    have coreStep := Step.ctxtFrame (f := caller.toCore) (n := fn.arity)
      (Step.ctxtLabel (n := fn.arity) (cont := []) lifted)
    simpa [coreConfig, coreCode, coreBody, expression_locals] using lift_instrs (saved.map Value.toCore) [] _ _ coreStep
  | fact fact =>
    cases fact with
    | enter saved args arity =>
      have step := Step.callRefFunc (P := P) (host := noHost) (f := caller.toCore)
        (vs := args.map Value.toCore) (c := .callRefType fn.type.toDefType) trivial allocated
        (signature fn) (by simp [Ty.length_ofList, arity]) rfl
      change Step P noHost _ ⟨s, caller.toCore, [.frame
        (Ty.ofList (fn.result.toList.map Ty.num)).length
        (Frame.forCall fn.module.toCore (args.map Value.toCore) fn.coreFunc.locals)
        [.label (Ty.ofList (fn.result.toList.map Ty.num)).length [] (expression fn.coreFunc.body)]]⟩ at step
      rw [armed_frame] at step
      simpa [coreConfig, coreCode, coreBody, vals_append, Ty.length_ofList, Callee.arity, Callee.coreFunc,
        List.append_assoc] using lift_instrs (saved.map Value.toCore) [] _ _ step
    | unreachable saved ls =>
      have step := Step.ctxtFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (n := fn.arity)
        (Step.ctxtLabel (n := fn.arity) (cont := []) (Step.parametric ParametricStep.unreachable))
      simpa [coreConfig, coreCode, coreBody, coreExit, Program.instructions, expression] using
        lift_instrs (saved.map Value.toCore) [] _ _ step
    | labelValues saved ls stack =>
      have step := Step.ctxtFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (n := fn.arity)
        (Step.labelVals (n := fn.arity) (cont := []) (vs := stack.map Value.toCore))
      simpa [coreConfig, coreCode, coreBody, coreExit, expression_locals, cv_encode] using
        lift_instrs (saved.map Value.toCore) [] _ _ step
    | labelReturn saved ls stack =>
      have step := Step.ctxtFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (n := fn.arity)
        (Step.returnLabel (n := fn.arity) (cont := []) (vs := stack.map Value.toCore) (rest := []))
      simpa [coreConfig, coreCode, coreBody, coreExit, expression_ret] using lift_instrs (saved.map Value.toCore) [] _ _ step
    | labelTrap saved ls =>
      have step := Step.ctxtFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (n := fn.arity) (Step.trapLabel (n := fn.arity) (cont := []))
      simpa [coreConfig, coreCode, coreBody, coreExit] using lift_instrs (saved.map Value.toCore) [] _ _ step
    | frameValues saved ls stack arity =>
      have step := Step.frameVals (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (vs := stack.map Value.toCore) (by simpa using arity)
      simpa [coreConfig, coreCode, coreBody, coreExit, vals_append] using lift_instrs (saved.map Value.toCore) [] _ _ step
    | frameReturn saved ls extra results arity =>
      have step := Step.returnFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (vs' := extra.map Value.toCore) (vs := results.map Value.toCore)
        (rest := []) (by simpa using arity)
      simpa [coreConfig, coreCode, coreBody, coreExit, vals_append, List.append_assoc] using
        lift_instrs (saved.map Value.toCore) [] _ _ step
    | frameTrap saved ls =>
      have step := Step.trapFrame (s := s) (f := caller.toCore) (fi := (fn.frame ls).toCore)
        (P := P) (host := noHost) (n := fn.arity)
      simpa [coreConfig, coreCode, coreBody, coreExit] using lift_instrs (saved.map Value.toCore) [] _ _ step
    | bubble saved discarded nonempty =>
      have step := Step.trapInstrs (s := s) (f := caller.toCore) (P := P) (host := noHost)
        (vs := discarded.map Value.toCore) (rest := []) (.inl (by simpa using nonempty))
      simpa [coreConfig, coreCode, coreBody, coreExit, vals_append, List.append_assoc] using
        lift_instrs (saved.map Value.toCore) [] _ _ step

private theorem cv_none {op : Admin} {xs : List Value} (none : op.val? = none) (mem : op ∈ cv xs) :
    False := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp mem
  simp at none

private theorem notValue_in_vals {op : Admin} {vs : List Val} (none : op.val? = none)
    (mem : op ∈ vals vs) : False := by
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp mem
  simp at none

private theorem callref_not_local {op : Admin} (kind : op.IsReturnCallRef)
    (supported : (Locals.coreCodec.read op).isSome) : False := by
  cases hr : Locals.coreCodec.read op with
  | none => simp [hr] at supported
  | some ins =>
    have eq := Locals.coreCodec.emit_read hr
    subst op
    cases ins with
    | value v => rcases v with ⟨t, bits⟩; cases t <;> contradiction
    | _ => contradiction

private theorem spine {a b : List Val} {op last : Admin} {tail : List Admin}
    (noOp : op.val? = none) (noLast : last.val? = none)
    (eq : vals a ++ [op] ++ tail = vals b ++ [last]) :
    a = b ∧ op = last ∧ tail = [] := by
  have head := congrArg fnv eq
  simpa [List.append_assoc, fnv_cons_of_none noOp, fnv_cons_of_none noLast] using head

theorem return_stuck {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {vs : List Val} {tail : List Admin} {target : Config H}
    (step : Step P noHost ⟨s, f, vals vs ++ .plain .return_ :: tail⟩ target) : False :=
  (not_step_blocked step (W := vs) (e := .plain .return_) (rest := tail)
    (by simp [fnv_cons_of_none (a := .plain .return_) rfl])) (.inr (.inl rfl))

theorem return_label_result {n : Nat} {stack : List Val} {tail out : List Admin}
    (pop : LabelExit n [] (vals stack ++ .plain .return_ :: tail) out) :
    out = vals stack ++ [.plain .return_] := by
  generalize shape : vals stack ++ .plain .return_ :: tail = code at pop
  have head := congrArg fnv shape
  simp only [fnv_vals_append, fnv_cons_of_none (a := .plain .return_) rfl] at head
  cases pop with
  | vals => simp at head
  | brZero | brSucc => simp [List.append_assoc, fnv_cons_of_none (a := .plain (.br _)) rfl] at head
  | ret =>
    have stackEq := congrArg Prod.fst head
    simp only [List.append_assoc, List.singleton_append, fnv_vals_append,
      fnv_cons_of_none (a := .plain .return_) rfl, List.append_nil] at stackEq
    rw [stackEq]
  | returnCall kind =>
    simp [fnv_cons_of_none (Admin.val?_of_isReturnCallRef kind)] at head
    exact (show ¬ (Admin.plain .return_).IsReturnCallRef from by simp [Admin.IsReturnCallRef])
      (head.2.1 ▸ kind) |>.elim
  | throw => simp [throwing, fnv_cons_of_none (a := .plain .throwRef) rfl] at head
  | trap => simp at head

theorem return_frame_iff {H : Type} {P : Profile} {s : Store H} {outer inner : Frame}
    {n : Nat} {extra results : List Val} {dst : Config H} (arity : results.length = n) :
    Step P noHost ⟨s, outer, [.frame n inner (vals (extra ++ results) ++ [.plain .return_])]⟩ dst ↔
      dst = ⟨s, outer, vals results⟩ := by
  constructor
  · intro step
    rcases step.frame_inv with ⟨_, _, _, inside, _⟩ | ⟨_, pop, rfl⟩
    · exact (return_stuck inside).elim
    generalize shape : vals (extra ++ results) ++ [Admin.plain .return_] = code at pop
    have head := congrArg fnv shape
    simp only [fnv_vals_append, fnv_cons_of_none (a := .plain .return_) rfl] at head
    cases pop with
    | vals => simp at head
    | @ret oldExtra oldResults rest count =>
      rw [← vals_append] at shape
      have stack := (spine (op := .plain .return_) (last := .plain .return_) rfl rfl shape.symm).1
      obtain ⟨_, rfl⟩ := returned_suffix stack (count.trans arity.symm)
      rfl
    | trap => simp at head
    | throw => simp [throwing, fnv_cons_of_none (a := .plain .throwRef) rfl] at head
    | returnCallNull kind | returnCallAddr kind _ _ _ =>
      have seen := congrArg (fun is => (fnv is).2) shape
      simp [List.append_assoc, fnv_cons_of_none (Admin.val?_of_isReturnCallRef kind)] at seen
      exact (show ¬ (Admin.plain .return_).IsReturnCallRef from by simp [Admin.IsReturnCallRef])
        (seen.1 ▸ kind) |>.elim
  · rintro rfl
    simpa only [vals_append, List.append_nil] using
      (Step.returnFrame (s := s) (f := outer) (fi := inner) (vs' := extra) (rest := []) arity)

private theorem exit_inner_stuck {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {ready : Exit} {dst : Config H} (h : Step P noHost ⟨s, f, coreExit ready⟩ dst) : False := by
  cases ready with
  | values stack => exact not_step_vals h
  | ret stack => exact return_stuck h
  | trap => exact Step.trap_stuck h

private theorem body_step {H : Type} {P : Profile} {s : Store H} {fn : Callee} {ls : List Value}
    {body : Body} {dst : Config H} (h : Step P noHost ⟨s, (fn.frame ls).toCore, coreBody body⟩ dst) :
    ∃ ls' next, (∀ saved, Edge fn (.label saved ls body) (.label saved ls' next)) ∧
      dst = ⟨s, (fn.frame ls').toCore, coreBody next⟩ := by
  cases body with
  | trap => exact (Step.trap_stuck h).elim
  | code p =>
    cases p with
    | locals code =>
      have localStep : Step P noHost (Locals.coreConfig s fn.module.toCore ⟨ls, code⟩) dst := by
        simpa [Locals.coreConfig, coreBody, expression_locals] using h
      obtain ⟨out, edge, same⟩ := Locals.core_step_iff.mp localStep
      exact ⟨out.locals, .code (.locals out.code), fun saved => reduce saved edge, by
        simpa [Locals.coreConfig, coreBody, expression_locals] using same⟩
    | ret stack =>
      have h' : Step P noHost ⟨s, (fn.frame ls).toCore, cv stack ++ [.plain .return_]⟩ dst := by
        simpa [coreBody, expression_ret] using h
      exact (return_stuck h').elim
    | unreachable =>
      exact ⟨ls, .trap, fun saved => fact (.unreachable saved ls), Step.unreachable_inv h⟩

private theorem reject_body {body : Body} {op : Admin} (none : op.val? = none)
    (different : op ≠ .plain .return_ ∧ op ≠ .plain .unreachable ∧ op ≠ .trap)
    (unread : ¬ (Locals.coreCodec.read op).isSome) (member : op ∈ coreBody body) : False := by
  cases body with
  | trap => exact different.2.2 (List.mem_singleton.mp member)
  | code p =>
    cases p with
    | locals code =>
      simp only [coreBody, expression_locals] at member
      exact unread (Locals.coreCodec.supports_encode code _ member)
    | ret stack =>
      simp only [coreBody, expression_ret, List.mem_append, List.mem_singleton] at member
      exact member.elim (cv_none none) different.1
    | unreachable => exact different.2.1 (List.mem_singleton.mp member)

private theorem label_pop {fn : Callee} (saved ls : List Value) {body : Body} {out : List Admin}
    (h : LabelExit fn.arity [] (coreBody body) out) :
    ∃ ready, Ground fn (.label saved ls body) (.exit saved ls ready) ∧ out = coreExit ready := by
  generalize eq : coreBody body = code at h
  cases h with
  | vals ws =>
    cases body with
    | trap => exact (notValue_in_vals (op := .trap) rfl (by rw [← eq]; exact List.Mem.head _)).elim
    | code p =>
      cases p with
      | locals code =>
        change expression ((Program.locals code).instructions Locals.coreInstr .return_ .unreachable) = _ at eq
        rw [expression_locals] at eq
        obtain ⟨xs, rfl⟩ := decode_numeric (eq ▸ Locals.coreCodec.supports_encode code)
        change Locals.coreCodec.encode code = cv xs at eq
        rw [← cv_encode] at eq
        have same := congrArg Locals.coreCodec.decode eq
        simp only [Locals.Codec.decode_encode] at same
        subst code
        exact ⟨.values xs, .labelValues saved ls xs, rfl⟩
      | ret stack =>
        change expression ((Program.ret stack).instructions Locals.coreInstr .return_ .unreachable) = _ at eq
        rw [expression_ret] at eq
        exact (notValue_in_vals (op := .plain .return_) rfl (by rw [← eq]; simp)).elim
      | unreachable =>
        exact (notValue_in_vals (op := .plain .unreachable) rfl (by rw [← eq]; exact List.Mem.head _)).elim
  | @ret vs tail =>
    have member : (.plain .return_ : Admin) ∈ coreBody body := by rw [eq]; simp
    cases body with
    | trap => simp [coreBody] at member
    | code p =>
      cases p with
      | locals code =>
        have check := Locals.coreCodec.supports_encode code
        rw [← expression_locals] at check
        exact Bool.noConfusion (check _ member)
      | ret actual =>
        change expression ((Program.ret actual).instructions Locals.coreInstr .return_ .unreachable) = _ at eq
        rw [expression_ret] at eq
        obtain ⟨rfl, _, rfl⟩ := spine rfl rfl eq.symm
        exact ⟨.ret actual, .labelReturn saved ls actual, rfl⟩
      | unreachable => simp [coreBody, Program.instructions, expression] at member
  | trap =>
    have member : (.trap : Admin) ∈ coreBody body := by rw [eq]; exact List.Mem.head _
    cases body with
    | trap => exact ⟨.trap, .labelTrap saved ls, rfl⟩
    | code p =>
      cases p with
      | locals code =>
        have check := Locals.coreCodec.supports_encode code
        rw [← expression_locals] at check
        exact Bool.noConfusion (check _ member)
      | ret stack =>
        simp only [coreBody, expression_ret, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at member
        exact (cv_none rfl member).elim
      | unreachable => simp [coreBody, Program.instructions, expression] at member
  | @brZero extra vs idx tail zero arity =>
    exact (reject_body (op := .plain (.br idx)) rfl (by simp) (fun h => Bool.noConfusion h)
      (by rw [eq]; simp)).elim
  | @brSucc vs idx tail pos =>
    exact (reject_body (op := .plain (.br idx)) rfl (by simp) (fun h => Bool.noConfusion h)
      (by rw [eq]; simp)).elim
  | throw a =>
    exact (reject_body (op := .plain .throwRef) rfl (by simp) (by decide)
      (by rw [eq]; simp [throwing])).elim
  | @returnCall vs op tail kind =>
    have noValue := IsReturnCallRef.val_none kind
    have different : op ≠ .plain .return_ ∧ op ≠ .plain .unreachable ∧ op ≠ .trap := by
      refine ⟨?_, ?_, ?_⟩ <;> intro eq <;> subst op <;> contradiction
    exact (reject_body noValue different (callref_not_local kind) (by rw [eq]; simp)).elim

private theorem reject_exit {ready : Exit} {op : Admin} (none : op.val? = none)
    (different : op ≠ .plain .return_ ∧ op ≠ .trap) (member : op ∈ coreExit ready) : False := by
  cases ready with
  | values stack => exact cv_none none member
  | ret stack =>
    simp only [coreExit, List.mem_append, List.mem_singleton] at member
    exact member.elim (cv_none none) different.1
  | trap => exact different.2 (List.mem_singleton.mp member)

private theorem frame_pop {H : Type} {s : Store H} {fn : Callee}
    (saved ls : List Value) {ready : Exit} {out : List Admin}
    (h : FrameExit s (fn.frame ls).toCore fn.arity (coreExit ready) out) :
    ∃ q, Ground fn (.exit saved ls ready) q ∧
      ∀ address, cv saved ++ out = coreCode address fn q := by
  generalize eq : coreExit ready = code at h
  cases h with
  | @vals vs arity =>
    cases ready with
    | values stack =>
      have same : stack.map Value.toCore = vs := vals_inj.mp eq
      subst vs
      exact ⟨.returned saved stack, .frameValues saved ls stack (by simpa using arity), by
        intro address; simp [coreCode, vals_append]⟩
    | ret stack =>
      exact (notValue_in_vals (op := .plain .return_) rfl (by rw [← eq]; simp [coreExit])).elim
    | trap => exact (notValue_in_vals (op := .trap) rfl (by rw [← eq]; exact List.Mem.head _)).elim
  | @ret extra vs tail arity =>
    cases ready with
    | values stack =>
      exact (cv_none (xs := stack) (op := .plain .return_) rfl (by
        change (.plain .return_ : Admin) ∈ coreExit (.values stack); rw [eq]; simp)).elim
    | trap =>
      have mem : (.plain .return_ : Admin) ∈ coreExit .trap := by rw [eq]; simp
      simp [coreExit] at mem
    | ret stack =>
      have shape : vals (extra ++ vs) ++ [.plain .return_] ++ tail =
          cv stack ++ [.plain .return_] := by simpa [coreExit, vals_append] using eq.symm
      obtain ⟨same, _, rfl⟩ := spine rfl rfl shape
      obtain ⟨discarded, results, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp same.symm
      exact ⟨.returned saved results, .frameReturn saved ls discarded results (by simpa using arity), by
        intro address; simp [coreCode, vals_append]⟩
  | trap =>
    cases ready with
    | values stack => exact (cv_none (xs := stack) (op := .trap) rfl (by
      change (.trap : Admin) ∈ coreExit (.values stack); rw [eq]; exact List.Mem.head _)).elim
    | ret stack =>
      have mem : (.plain .return_ : Admin) ∈ ([.trap] : List Admin) := by rw [← eq]; simp [coreExit]
      simp at mem
    | trap => exact ⟨.trapped saved, .frameTrap saved ls, fun _ => rfl⟩
  | throw a =>
    exact (reject_exit (op := .plain .throwRef) rfl (by simp) (by rw [eq]; simp [throwing])).elim
  | @returnCallNull vs op tail kind =>
    have different : op ≠ .plain .return_ ∧ op ≠ .trap := by
      refine ⟨?_, ?_⟩ <;> intro eq <;> subst op <;> contradiction
    exact (reject_exit (IsReturnCallRef.val_none kind) different (by rw [eq]; simp)).elim
  | @returnCallAddr extra vs addr op tail fn' ps rs kind hf he hn =>
    have different : op ≠ .plain .return_ ∧ op ≠ .trap := by
      refine ⟨?_, ?_⟩ <;> intro eq <;> subst op <;> contradiction
    exact (reject_exit (IsReturnCallRef.val_none kind) different (by rw [eq]; simp)).elim

private theorem frame_label_no_pop {H : Type} {s : Store H} {inner : Frame} {arity : Nat}
    {body out : List Admin}
    (h : FrameExit s inner arity [.label arity [] body] out) : False := by
  generalize eq : ([.label arity [] body] : List Admin) = code at h
  cases h with
  | vals =>
    exact notValue_in_vals (op := .label arity [] body) rfl (by rw [← eq]; exact List.Mem.head _)
  | returnCallNull kind | returnCallAddr kind _ _ _ =>
    have first := congrArg fnv eq
    have none := IsReturnCallRef.val_none kind
    simp [fnv_cons_of_none none, fnv_cons_of_none (a := .label arity [] body) rfl] at first
  | _ =>
    have first := congrArg fnv eq
    simp [fnv_cons_of_none (a := .label arity [] body) rfl, throwing] at first

private theorem frame_cases {H : Type} {P : Profile} {s : Store H} {caller inner : Frame}
    {saved : List Value} {arity : Nat} {code : List Admin} {dst : Config H}
    (h : Step P noHost ⟨s, caller, cv saved ++ [.frame arity inner code]⟩ dst) :
    (∃ s' inner' rest, Step P noHost ⟨s, inner, code⟩ ⟨s', inner', rest⟩ ∧
      dst = ⟨s', caller, cv saved ++ [.frame arity inner' rest]⟩) ∨
    (∃ rest, FrameExit s inner arity code rest ∧ dst = ⟨s, caller, cv saved ++ rest⟩) := by
  obtain ⟨mid, one, result⟩ := Step.ctx_in_seq (X := .frame arity inner code) (rest := []) (by trivial) h
  rcases one.frame_inv with ⟨s', inner', code', h, rfl⟩ | ⟨out, pop, rfl⟩
  · exact .inl ⟨s', inner', code', h, by simpa using result⟩
  · exact .inr ⟨out, pop, by simpa using result⟩

private theorem bubble_readback {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {saved : List Value} {dst : Config H}
    (step : Step P noHost ⟨s, f, cv saved ++ [.trap]⟩ dst) :
    ∃ kept discarded : List Value, saved = kept ++ discarded ∧ discarded ≠ [] ∧
      dst = ⟨s, f, cv kept ++ [.trap]⟩ := by
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with hd | hb
  · obtain ⟨_, _, e, _, _, first, _, head, _⟩ := fnv_headDec hd
    have same := congrArg Prod.snd first
    change (fnv (cv saved ++ [.trap])).2 = _ at same
    simp at same
    exact (head.good.ne_trap same.1.symm).elim
  · obtain ⟨p, q, u, rest, nonempty, ⟨first, _, rfl⟩ | ⟨a, first, _, _⟩⟩ := fnv_bubble hb
    · change fnv (cv saved ++ [.trap]) = _ at first
      have same : saved.map Value.toCore = p ++ q ∧ u = [] ∧ rest = [] := by
        simpa only [fnv_vals_append, fnv_trap_cons, List.append_nil, Prod.mk.injEq, List.cons.injEq,
          List.nil_eq_append_iff, true_and] using first
      obtain ⟨sameStack, rfl, rfl⟩ := same
      obtain ⟨kept, discarded, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp sameStack
      refine ⟨kept, discarded, rfl, ?_, by simp⟩
      intro empty
      subst discarded
      exact nonempty.elim (fun h => h rfl) (fun h => h rfl)
    · change fnv (cv saved ++ [.trap]) = _ at first
      simp at first

theorem core_readback {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {address : FuncAddr} {fn : Callee} (allocated : s.funcs[address.value]? = some fn.coreInstance)
    {a : State} {dst : Config H} (ready : Admitted fn a)
    (step : Step P noHost (coreConfig s caller address fn a) dst) :
    ∃ out, Edge fn a out ∧ dst = coreConfig s caller address fn out := by
  cases a with
  | invoke saved args =>
    have invoke : Step P noHost ⟨s, caller.toCore, cv (saved ++ args) ++
        [.ref (.func address.value), .callRefType fn.type.toDefType]⟩ dst := step
    obtain ⟨kept, used, ps, rs, sameStack, expanded, arity, eq⟩ :=
      Step.callRef_wasm_inv (fi := fn.coreInstance) (code := fn.coreFunc)
        (by trivial) allocated rfl invoke
    have expected := Expand.iff.mp (signature fn)
    change Expand fn.type.toDefType (.func ps rs) at expanded
    have sameType := (Expand.iff.mp expanded).symm.trans expected
    have sameType := Option.some.inj sameType
    injection sameType with sameParams sameResults
    subst ps
    subst rs
    have argc : args.length = fn.params.length := by simpa using congrArg List.length ready.1
    have stackEq : saved.map Value.toCore ++ args.map Value.toCore = kept ++ used := by
      simpa only [List.map_append] using sameStack
    obtain ⟨rfl, rfl⟩ := returned_suffix stackEq
      (show (args.map Value.toCore).length = used.length by simpa [Ty.length_ofList, argc] using arity.symm)
    change dst = ⟨s, caller.toCore, cv saved ++
      [.frame (Ty.ofList (fn.result.toList.map Ty.num)).length
        (Frame.forCall fn.module.toCore (args.map Value.toCore) fn.coreFunc.locals)
        [.label (Ty.ofList (fn.result.toList.map Ty.num)).length [] (expression fn.coreFunc.body)]]⟩ at eq
    rw [armed_frame] at eq
    exact ⟨.label saved (fn.init args) (.code fn.program), fact (.enter saved args argc), by
      simpa [coreConfig, coreCode, coreBody, Ty.length_ofList, Callee.coreFunc, Callee.arity] using eq⟩
  | label saved ls body =>
    rcases frame_cases (saved := saved) step with ⟨s', inner, code, innerStep, eq⟩ | ⟨out, pop, eq⟩
    · let outer (c : Config H) : Config H :=
        ⟨c.store, caller.toCore, cv saved ++ [.frame fn.arity c.frame c.code]⟩
      rcases innerStep.label_inv with ⟨s'', frame'', code'', h, labelled⟩ | ⟨rest, pop, labelled⟩
      · obtain ⟨ls', next, move, same⟩ := body_step h
        let wrap (c : Config H) : Config H :=
          ⟨c.store, caller.toCore, cv saved ++ [.frame fn.arity c.frame [.label fn.arity [] c.code]]⟩
        exact ⟨.label saved ls' next, move saved,
          eq.trans ((congrArg outer labelled).trans (congrArg wrap same))⟩
      · obtain ⟨next, move, rfl⟩ := label_pop saved ls pop
        exact ⟨.exit saved ls next, fact move, eq.trans (congrArg outer labelled)⟩
    · exact (frame_label_no_pop pop).elim
  | exit saved ls ready =>
    rcases frame_cases (saved := saved) step with ⟨_, _, _, h, _⟩ | ⟨out, pop, eq⟩
    · exact (exit_inner_stuck h).elim
    · obtain ⟨q, rule, code⟩ := frame_pop saved ls pop
      exact ⟨q, fact rule, eq.trans (congrArg (fun code => (⟨s, caller.toCore, code⟩ : Config H)) (code address))⟩
  | returned saved results => exact (Step.not_vals step).elim
  | trapped saved =>
    obtain ⟨kept, discarded, rfl, ne, eq⟩ := bubble_readback step
    exact ⟨.trapped kept, fact (.bubble kept discarded ne), eq⟩

end Silmaril.Wasm.Institution.Operational.CallFrame.Proofs
