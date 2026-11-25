module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Context
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.NativeCommon
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Core

open Execution.Core
open Execution
open Execution.Runtime (FuncAddr Value)
open Computed
open Wasm.Numerics (Profile)
open Wasm.SingleThreaded.Det (noHost)

private abbrev native {H : Type} (P : Profile) := Step (H := H) P noHost

private theorem expression_code (fn : Function) :
    expression fn.coreFunc.body = (Body.running fn.initial fn.code).render coreAdmin := by
  change expression (fn.instructions Sequence.coreSource (Locals.coreInstr ∘ .set) (Locals.coreInstr ∘ .tee) .unreachable) = _
  rw [Function.instructions, expression, List.map_append]
  change (fn.initial.map Sequence.coreSource.value).map Admin.plain ++
      (fn.code.map (Op.emit Sequence.coreSource (Locals.coreInstr ∘ .set) (Locals.coreInstr ∘ .tee) .unreachable)).map Admin.plain =
    coreValues fn.initial ++ fn.code.map coreAdmin.emit
  unfold coreValues vals
  simp only [List.map_map]
  congr 1
  · apply List.map_congr_left
    intro v _
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  · apply List.map_congr_left
    intro op _
    cases op with
    | numeric op => cases op <;> rfl
    | set | tee | call | unreachable => rfl

private theorem values_append (xs ys : List Value) :
    coreValues (xs ++ ys) = coreValues xs ++ coreValues ys := by
  simp only [coreValues, List.map_append, vals_append]

private theorem attach_code (saved : List Value) (target : CallTarget) (rest : List Op) (q : Phase) :
    (Body.attach saved target rest q).render coreAdmin =
      coreValues saved ++ q.render coreAdmin target ++ rest.map coreAdmin.emit :=
  render_attach values_append saved target rest q

private theorem lift_label {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {parent parentNext : Frame} {n : Nat} {before after : List Admin}
    (move : native P ⟨s, parent, before⟩ ⟨s, parentNext, after⟩) :
    native P ⟨s, caller.toCore, [.frame n parent [.label n [] before]]⟩
      ⟨s, caller.toCore, [.frame n parentNext [.label n [] after]]⟩ :=
  .ctxtFrame (.ctxtLabel move)

private theorem set_sound {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals next saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .set idx]⟩ ⟨next, []⟩) :
    native P ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v]) (.set idx :: rest)).render coreAdmin⟩
      ⟨s, (currentFrame decl next).toCore, (Body.running saved rest).render coreAdmin⟩ := by
  have move := Locals.core_sound (P := P) (s := s) (m := decl.module.toCore) write
  have lifted := Wasm.SingleThreaded.Det.lift_instrs (saved.map Value.toCore) (rest.map coreAdmin.emit) _ _ move
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.coreConfig, Locals.Codec.encode, Locals.coreCodec, Locals.coreInstr,
    Execution.Runtime.Frame.toCore, currentFrame, Body.render, coreAdmin, Syntax.emit, Op.emit,
    coreValues, vals, List.map_append, List.append_assoc, Function.comp_def] at lifted ⊢ <;> exact lifted

private theorem tee_sound {H : Type} {P : Profile} {s : Store H} {decl : Declaration}
    {locals saved : List Value} {v : Value} {idx : LocalIdx} {rest : List Op}
    (write : Locals.Edge ⟨locals, [.value v, .tee idx]⟩ ⟨locals, [.value v, .value v, .set idx]⟩) :
    native P ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v]) (.tee idx :: rest)).render coreAdmin⟩
      ⟨s, (currentFrame decl locals).toCore, (Body.running (saved ++ [v, v]) (.set idx :: rest)).render coreAdmin⟩ := by
  have move := Locals.core_sound (P := P) (s := s) (m := decl.module.toCore) write
  have lifted := Wasm.SingleThreaded.Det.lift_instrs (saved.map Value.toCore) (rest.map coreAdmin.emit) _ _ move
  rcases v with ⟨t, bits⟩
  cases t <;> simp [Locals.coreConfig, Locals.Codec.encode, Locals.coreCodec, Locals.coreInstr,
    Execution.Runtime.Frame.toCore, currentFrame, Body.render, coreAdmin, Syntax.emit, Op.emit,
    coreValues, vals, List.map_append, List.append_assoc, Function.comp_def] at lifted ⊢ <;> exact lifted

private theorem entry_iff {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame}
    {fn : Function} {target : CallTarget} {saved args : List Value} {rest : List Admin} {dst : Config H}
    (declared : fn.declaration = target.declaration)
    (alloc : s.funcs[target.address.value]? = some fn.coreInstance)
    (typed : args.map Value.type = fn.declaration.params) :
    native P ⟨s, caller.toCore, coreValues (saved ++ args) ++ .ref (.func target.address.value) ::
        .callRefType target.declaration.type.toDefType :: rest⟩ dst ↔
      dst = ⟨s, caller.toCore, coreValues saved ++
        (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render coreAdmin target ++ rest⟩ := by
  have enter := Sequence.wasm_entry_context_iff (P := P) (caller := caller) (saved := saved) (rest := rest) (dst := dst)
    alloc typed
  have init := Sequence.core_frame_forCall fn.declaration.module args fn.declaration.locals
  change Frame.forCall fn.declaration.module.toCore (args.map Value.toCore) fn.coreFunc.locals =
    (fn.declaration.frame args).toCore at init
  rw [init, expression_code] at enter
  rw [Phase.render, ← declared]
  simpa only [List.append_assoc, List.singleton_append, coreAdmin, Declaration.type, currentFrame, Declaration.frame] using enter

private theorem running_stays {n : Nat} {v : List Value} {op : Op} {rest : List Op} {out : List Admin}
    (pop : LabelExit n [] ((Body.running v (op :: rest)).render coreAdmin) out) : False := by
  change LabelExit n [] (coreValues v ++ coreAdmin.emit op :: rest.map coreAdmin.emit) out at pop
  cases op with
  | numeric p =>
    cases p <;> exact Computed.core_label_stays (head := coreAdmin.emit (.numeric _)) (by rfl)
      (by simp [Syntax.emit, Op.emit, coreAdmin, Prefix.emit, coreSyntax])
      (by simp [Syntax.emit, Op.emit, coreAdmin, Prefix.emit, coreSyntax])
      (by simp [Syntax.emit, Op.emit, coreAdmin, Prefix.emit, coreSyntax, Admin.IsReturnCallRef])
      (by simp [Syntax.emit, Op.emit, coreAdmin, Prefix.emit, coreSyntax])
      (by simp [Syntax.emit, Op.emit, coreAdmin, Prefix.emit, coreSyntax]) pop
  | set idx =>
    exact Computed.core_label_stays (head := .plain (.localSet idx)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | tee idx =>
    exact Computed.core_label_stays (head := .plain (.localTee idx)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | call t =>
    exact Computed.core_label_stays (head := .plain (.call t.index)) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop
  | unreachable =>
    exact Computed.core_label_stays (head := .plain .unreachable) rfl
      (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp) pop

private theorem active_entered_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.check = true)
    {caller : Runtime.Frame} {root target : CallTarget} {fn : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    {locals saved : List Value} {rest : List Op} {child : Phase} (live : child.Active)
    {k : Nat} {f : Frame} {code : List Admin} (rendered : child.render coreAdmin target = [.frame k f code])
    (childStep : ∀ {dst}, native P (coreConfig s (currentFrame root.declaration locals) target child) dst ↔
      ∃ out, program.Edge checked target.address child out ∧ dst = coreConfig s (currentFrame root.declaration locals) target out)
    {dst : Config H} :
    native P (coreConfig s caller root (.label locals (.active saved target child rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target child rest)) out ∧
        dst = coreConfig s caller root out := by
  have ctx : native P (coreConfig s caller root (.label locals (.active saved target child rest))) dst ↔
      ∃ mid, native P (coreConfig s (currentFrame root.declaration locals) target child) mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame root.declaration.results.length mid.frame
          [.label root.declaration.results.length [] (coreValues saved ++ mid.code ++ rest.map coreAdmin.emit)]]⟩ := by
    change native P ⟨s, caller.toCore, [.frame root.declaration.results.length (currentFrame root.declaration locals).toCore
        [.label root.declaration.results.length [] (coreValues saved ++ child.render coreAdmin target ++ rest.map coreAdmin.emit)]]⟩ dst ↔
      ∃ mid, native P ⟨s, (currentFrame root.declaration locals).toCore, child.render coreAdmin target⟩ mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame root.declaration.results.length mid.frame
          [.label root.declaration.results.length [] (coreValues saved ++ mid.code ++ rest.map coreAdmin.emit)]]⟩
    rw [rendered, List.append_assoc, List.singleton_append]
    exact core_entered_child_iff (saved := saved.map Value.toCore)
  rw [ctx]
  constructor
  · rintro ⟨mid, move, rfl⟩
    obtain ⟨out, childEdge, rfl⟩ := childStep.mp move
    refine ⟨.label locals (Body.attach saved target rest out),
      (program.active_iff checked found used live).mpr ⟨out, childEdge, rfl⟩, ?_⟩
    change _ = (⟨s, caller.toCore, [.frame _ _ [.label _ [] ((Body.attach saved target rest out).render coreAdmin)]]⟩ : Config H)
    rw [attach_code]
    rfl
  · rintro ⟨out, move, rfl⟩
    obtain ⟨childOut, childEdge, rfl⟩ := (program.active_iff checked found used live).mp move
    refine ⟨_, childStep.mpr ⟨childOut, childEdge, rfl⟩, ?_⟩
    change (⟨s, caller.toCore, [.frame _ _ [.label _ [] ((Body.attach saved target rest childOut).render coreAdmin)]]⟩ : Config H) = _
    rw [attach_code]
    rfl

private theorem under_label_iff {H : Type} {P : Profile} {s : Store H} {caller : Runtime.Frame} {parent : Frame} {n : Nat}
    {code : List Admin} {dst : Config H}
    (stays : ∀ {out}, LabelExit n [] code out → False) :
    native P ⟨s, caller.toCore, [.frame n parent [.label n [] code]]⟩ dst ↔
      ∃ mid : Config H, native P ⟨s, parent, code⟩ mid ∧
        dst = ⟨mid.store, caller.toCore, [.frame n mid.frame [.label n [] mid.code]]⟩ := by
  constructor
  · intro move
    rcases Computed.core_body_step_cases move with inside | ⟨_, pop, _⟩
    · exact inside
    · exact (stays pop).elim
  · rintro ⟨⟨_, _, _⟩, move, rfl⟩
    exact .ctxtFrame (.ctxtLabel move)

private theorem pending_child_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.CoreAllocated s) {caller : Runtime.Frame} {root target : CallTarget} {fn callee : Function}
    (found : program.lookup root.address = some fn) (used : target ∈ fn.targets)
    (childFound : program.lookup target.address = some callee) (declared : callee.declaration = target.declaration)
    {locals saved operands : List Value} {rest : List Op} (typed : operands.map Value.type = callee.declaration.params)
    {dst : Config H} :
    native P (coreConfig s caller root (.label locals (.active saved target (.invoke operands) rest))) dst ↔
      ∃ out, program.Edge checked root.address (.label locals (.active saved target (.invoke operands) rest)) out ∧
        dst = coreConfig s caller root out := by
  let head := Admin.callRefType target.declaration.type.toDefType
  let ref := Val.ref (.func target.address.value)
  have stays {out : List Admin} (pop : LabelExit root.declaration.results.length []
      (coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit) out) :
      False := by
    have prefixed : vals ((saved ++ operands).map Value.toCore ++ [ref]) ++ head :: rest.map coreAdmin.emit =
        coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit := by
      rw [vals_append, List.append_assoc]
      rfl
    rw [← prefixed] at pop
    exact Computed.core_label_stays (head := head) rfl (by simp [head]) (by simp [head])
      (by simp [head, Admin.IsReturnCallRef]) (by simp [head]) (by simp [head]) pop
  have ctx := under_label_iff (P := P) (s := s) (caller := caller)
    (parent := (currentFrame root.declaration locals).toCore) (dst := dst) stays
  have entry {mid : Config H} := entry_iff (P := P) (caller := currentFrame root.declaration locals) (saved := saved)
    (rest := rest.map coreAdmin.emit) (dst := mid) declared (allocated _ _ childFound) typed
  have live : (Phase.invoke operands).Active := trivial
  have source : (Body.active saved target (.invoke operands) rest).render coreAdmin =
      coreValues (saved ++ operands) ++ .ref (.func target.address.value) :: head :: rest.map coreAdmin.emit := by
    change coreValues saved ++ (coreValues operands ++ [.ref (.func target.address.value), head]) ++ rest.map coreAdmin.emit = _
    rw [values_append]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  change native P ⟨s, caller.toCore, [.frame _ _ [.label _ [] ((Body.active saved target (.invoke operands) rest).render coreAdmin)]]⟩ dst ↔ _
  rw [source, ctx]
  constructor
  · rintro ⟨mid, move, eq⟩
    obtain rfl := entry.mp move
    refine ⟨_, (program.active_iff checked found used live).mpr
      ⟨_, (program.edge_iff checked childFound).mpr (.enter operands typed), rfl⟩, ?_⟩
    exact eq
  · rintro ⟨out, edge, rfl⟩
    obtain ⟨childOut, step, rfl⟩ := (program.active_iff checked found used live).mp edge
    cases (program.edge_iff checked childFound).mp step with
    | enter _ _ => exact ⟨_, entry.mpr rfl, rfl⟩

private theorem trapped_not_final {n : Nat} {stack : List Value} {rest : List Op}
    {out : List Admin} (pop : LabelExit n [] ((Body.trapped stack rest).render coreAdmin) out) :
    stack = [] ∧ rest = [] := by
  by_contra unfinished
  exact Computed.core_label_stays (head := .trap) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef])
    (by simp) (fun _ => by simpa using not_and_or.mp unfinished) pop

theorem step_iff {H : Type} {P : Profile} {s : Store H} {program : Program} (checked : program.check = true)
    (allocated : program.CoreAllocated s) (address : FuncAddr) :
    ∀ {caller target fn a dst}, (addr : target.address = address) →
      Root program caller target fn → Admitted program fn a →
      (Step P noHost (coreConfig s caller target a) dst ↔
        ∃ out, program.Edge checked target.address a out ∧ dst = coreConfig s caller target out) := by
  induction address using (program.table.wellFounded (Program.rankCheck checked)).induction with
  | h address ih =>
    intro caller target fn a dst addr root ready
    subst address
    have rule {a b : Phase} := program.edge_iff checked (a := a) (b := b) root.found
    have callLookup : caller.module.funcs[target.index.toNat]? = some target.address := root.resolves
    have alloc := allocated _ _ root.found
    have coreType : (fn.coreInstance (H := H)).type = target.declaration.type.toDefType :=
      congrArg (fun d => d.type.toDefType) root.declared
    cases ready with
    | @call _ args typed =>
      have move {next : Config H} := Computed.core_direct_call_iff (s := s) (P := P) (stack := args)
        (tail := []) (dst := next) callLookup alloc
      constructor
      · intro h
        refine ⟨_, rule.mpr (.resolve args), ?_⟩
        rw [coreType] at move
        exact move.mp h
      · rintro ⟨out, h, rfl⟩
        cases rule.mp h with
        | resolve =>
          rw [coreType] at move
          exact move.mpr rfl
    | @invoke _ args typed =>
      have move {next : Config H} := entry_iff (P := P) (caller := caller) (saved := []) (rest := []) (dst := next)
        root.declared alloc typed
      constructor
      · intro step
        refine ⟨_, rule.mpr (.enter args typed), ?_⟩
        exact (move.mp step).trans (by simp [coreValues, vals, coreConfig])
      · rintro ⟨out, step, rfl⟩
        cases rule.mp step with
        | enter =>
          change native P ⟨s, caller.toCore, coreValues args ++
              [.ref (.func target.address.value), .callRefType target.declaration.type.toDefType]⟩
            ⟨s, caller.toCore, (Phase.label (fn.declaration.frame args).locals (.running fn.initial fn.code)).render coreAdmin target⟩
          simpa only [coreValues, vals, List.map_nil, List.nil_append, List.append_nil] using move.mpr rfl
    | @running _ locals stack rest typed codeTyped =>
      cases rest with
      | nil =>
        constructor
        · intro move
          rcases Computed.core_body_step_cases move with ⟨_, inside, _⟩ | ⟨_, pop, eq⟩
          · exact (Nested.core_result_stuck (r := .values stack) (by simpa only [Body.render, coreAdmin,
              List.map_nil, List.append_nil, Nested.resultCode] using inside)).elim
          · exact ⟨_, rule.mpr (.leaveValues locals stack), eq.trans (by
              have leave := Nested.core_label_result (r := .values stack)
                (by simpa only [Body.render, coreAdmin, List.map_nil, List.append_nil, Nested.resultCode] using pop)
              rw [leave]
              rfl)⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | leaveValues =>
            simpa only [coreConfig, Phase.render, Body.render, coreAdmin, List.map_nil, List.append_nil, Nested.resultCode] using
              Step.ctxtFrame (f := caller.toCore) (n := target.declaration.results.length)
                (Step.labelVals (P := P) (host := noHost) (cont := []) (n := target.declaration.results.length)
                  (vs := stack.map Value.toCore) (s := s) (f := (currentFrame target.declaration locals).toCore))
      | cons op rest =>
        have stays {out : List Admin} := running_stays (n := target.declaration.results.length) (v := stack) (op := op) (rest := rest) (out := out)
        constructor
        · intro move
          obtain ⟨mid, inner, eq⟩ := (under_label_iff stays).mp move
          cases op with
          | numeric op =>
            have reduction := (Prefix.core_step_iff (f := currentFrame target.declaration locals) (op := op) (tail := rest.map coreAdmin.emit)).mp inner
            obtain ⟨answer, reduce, rfl⟩ := reduction
            exact ⟨_, rule.mpr (.numeric reduce), eq.trans (by cases answer <;> rfl)⟩
          | set idx =>
            obtain ⟨saved, value, next, rfl, write, rfl⟩ := Computed.core_set_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localSet write), eq⟩
          | tee idx =>
            obtain ⟨saved, value, rfl, write, rfl⟩ := Computed.core_tee_read (f := currentFrame target.declaration locals) inner
            exact ⟨_, rule.mpr (.localTee write), eq⟩
          | call child =>
            obtain ⟨saved, operands, rfl, used, count⟩ := split_call codeTyped
            obtain ⟨callee, childFound, declared, resolves⟩ := program.linked_target checked root.found used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← root.declared] using resolves
            have call := (Computed.core_direct_call_iff (stack := saved ++ operands)
              (tail := rest.map coreAdmin.emit) h (allocated _ _ childFound)).mp inner
            have signature : (callee.coreInstance (H := H)).type = child.declaration.type.toDefType :=
              congrArg (fun d => d.type.toDefType) declared
            rw [signature] at call
            subst mid
            exact ⟨_, rule.mpr (.dispatch locals saved operands child rest used count), eq.trans (by
              simp only [coreConfig, Phase.render, Body.render, coreAdmin, values_append,
                List.append_assoc, List.cons_append, List.nil_append])⟩
          | unreachable =>
            obtain rfl := (Computed.core_unreachable_iff (stack := stack.map Value.toCore)).mp inner
            exact ⟨_, rule.mpr (.unreachable locals stack rest), eq⟩
        · rintro ⟨out, move, rfl⟩
          cases rule.mp move with
          | @numeric locals stack op rest answer reduce =>
            apply lift_label
            exact (Prefix.core_step_iff (P := P) (s := s) (f := currentFrame target.declaration locals) (stack := stack)
              (op := op) (tail := rest.map coreAdmin.emit)).mpr ⟨answer, reduce, by cases answer <;> rfl⟩
          | @localSet locals next saved i value rest write =>
            exact lift_label (set_sound write)
          | @localTee locals saved i value rest write =>
            exact lift_label (tee_sound write)
          | dispatch _ saved operands child rest used count =>
            obtain ⟨callee, childFound, declared, resolves⟩ := program.linked_target checked root.found used
            have h : (currentFrame target.declaration locals).module.funcs[child.index.toNat]? = some child.address := by
              simpa only [currentFrame, ← root.declared] using resolves
            have signature : (callee.coreInstance (H := H)).type = child.declaration.type.toDefType :=
              congrArg (fun d => d.type.toDefType) declared
            have step {dst : Config H} := Computed.core_direct_call_iff (P := P) (stack := saved ++ operands)
              (tail := rest.map coreAdmin.emit) (dst := dst) h (allocated _ _ childFound)
            rw [signature] at step
            apply lift_label
            simpa only [Body.render, Phase.render, coreAdmin, Syntax.emit, Op.emit, coreSyntax, Function.comp_def,
              values_append, List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using step.mpr rfl
          | unreachable =>
            exact lift_label (Computed.core_unreachable_iff.mpr rfl)
    | @active _ locals saved child q rest callee typed used childFound declared live childReady resume =>
      obtain ⟨_, _, _, resolves⟩ := program.linked_target checked root.found used
      have childResolves : child.Resolves (currentFrame target.declaration locals) := by
        simpa only [CallTarget.Resolves, currentFrame, ← root.declared] using resolves
      have childStep {next : Config H} := ih child.address (program.target_resolved checked root.found used)
        (dst := next) rfl ⟨childFound, declared, childResolves⟩ childReady
      cases q with
      | call | done => cases live
      | invoke operands =>
        cases childReady with
        | invoke localsTyped => exact pending_child_iff checked allocated root.found used childFound declared localsTyped
      | label | exit => exact active_entered_iff checked root.found used live rfl childStep
    | @trapped _ locals saved rest typed =>
      constructor
      · intro move
        rcases Computed.core_body_step_cases move with ⟨mid, inside, eq⟩ | ⟨_, pop, eq⟩
        · obtain ⟨kept, remaining, cut, rfl⟩ := (Prefix.core_discard_iff (f := currentFrame target.declaration locals) coreAdmin.emit).mp inside
          exact ⟨_, rule.mpr (.discard cut), eq⟩
        · obtain ⟨rfl, rfl⟩ := trapped_not_final pop
          exact ⟨_, rule.mpr (.leaveTrap locals), eq.trans (by rw [Nested.core_label_result (r := .trap) pop]; rfl)⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | discard cut => exact lift_label ((Prefix.core_discard_iff (f := currentFrame target.declaration locals) coreAdmin.emit).mpr ⟨_, _, cut, rfl⟩)
        | leaveTrap => exact .ctxtFrame .trapLabel
    | @exit _ locals result typed outTyped =>
      constructor
      · intro move
        exact ⟨_, rule.mpr (.leaveFrame locals result outTyped), Nested.core_frame_result (caller := caller) (r := result) move⟩
      · rintro ⟨out, move, rfl⟩
        cases rule.mp move with
        | leaveFrame =>
          cases result with
          | trap => exact .trapFrame
          | values xs =>
            exact .frameVals (vs := xs.map Value.toCore) (by
              simpa using (result_length outTyped).trans (congrArg (fun d => d.results.length) root.declared))
    | @done _ result typed =>
      constructor
      · intro step
        exact (Nested.core_result_stuck (r := result) step).elim
      · rintro ⟨_, step, _⟩
        cases rule.mp step

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs.Core
