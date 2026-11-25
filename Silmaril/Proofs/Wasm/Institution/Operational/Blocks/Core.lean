module

public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Proofs

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Runtime (Value)
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Validation (Ty)

private theorem encode_values (vs : List Value) :
    Locals.coreCodec.encode (Locals.values vs) = vals (vs.map LegacyDivision.liftValue) := by
  have emit (v : Value) : Locals.coreCodec.emit (.value v) = (LegacyDivision.liftValue v).toAdmin := by
    rcases v with ⟨t, bits⟩
    cases t <;> rfl
  simp [Locals.Codec.encode, Locals.values, vals, List.map_map, emit]

private theorem encode_body (ops : List Locals.Op) :
    expression (ops.map Locals.coreInstr) = Locals.coreCodec.encode ops := List.map_map

private theorem resolve (m : ModuleInst) (result : Option NumType) :
    m.blockType? (coreType result) = some ([], result.toList.map Ty.num) := by
  cases result <;> rfl

theorem core_sound {H : Type} {P : Profile} (s : Store H) (m : ModuleInst)
    {a b : State} (h : Edge a b) : Step P noHost (coreConfig s m a) (coreConfig s m b) := by
  rcases invert h with ⟨result, body, rfl, rfl⟩ |
    ⟨result, before, after, rfl, rfl, innerEdge⟩ | ⟨result, ls, vs, rfl, rfl⟩
  · simpa [coreConfig, encode_body, vals] using
      (Step.block (P := P) (host := noHost) (s := s) (f := ⟨body.locals.map Locals.coreLocal, m⟩)
        (body := body.code.map Locals.coreInstr) (vs := []) (resolve m result) rfl)
  · exact .ctxtLabel (Locals.core_sound innerEdge)
  · simpa [coreConfig, encode_values] using
      (Step.labelVals (P := P) (host := noHost) (s := s) (f := ⟨ls.map Locals.coreLocal, m⟩)
        (n := result.toList.length) (cont := []) (vs := vs.map LegacyDivision.liftValue))

private theorem singleton_head {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {op : Admin} {b : Config H} (step : Step P noHost ⟨s, f, [op]⟩ b)
    (value : op.val? = none) (trap : op ≠ .trap) (throws : op ≠ .plain .throwRef) :
    Head P s f [] op b := by
  have first : fnv [op] = ([], [op]) := fnv_cons_of_none value []
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨saved, args, op', tail, next, eq, _, hh, rfl⟩ := fnv_headDec head
    rw [first] at eq
    simp only [Prod.mk.injEq, List.nil_eq_append_iff, List.cons.injEq] at eq
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := eq
    simpa [vals] using hh
  · obtain ⟨_, _, _, _, _, ⟨eq, _, _⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble <;>
      rw [first] at eq <;> simp_all

private theorem head_block {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {result : Option NumType} {body : List Instr} {b : Config H} {args : List Val}
    (head : Head P s f args (.plain (.block (coreType result) body)) b) :
    args = [] ∧ b = ⟨s, f, [.label result.toList.length [] (expression body)]⟩ := by
  cases head with
  | block found arity =>
    rw [resolve] at found
    cases found
    have empty := List.eq_nil_of_length_eq_zero arity
    subst args
    simp [vals]
  | _ =>
    first
    | have hf := (famOf_of_shape (ParametricStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (NumericStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (VectorStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (VariableStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (TableStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (MemoryStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (RefStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (AggregateStep.shape ‹_›)).2; contradiction
    | contradiction

theorem core_entry_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {result : Option NumType} {body : List Instr} {dst : Config H} :
    Step P noHost ⟨s, f, [.plain (.block (coreType result) body)]⟩ dst ↔
      dst = ⟨s, f, [.label result.toList.length [] (expression body)]⟩ := by
  constructor
  · intro step
    exact (head_block (singleton_head step rfl (by simp) (by simp))).2
  · rintro rfl
    simpa only [vals, List.map_nil, List.nil_append, List.length_map] using
      Step.block (P := P) (host := noHost) (s := s) (body := body) (vs := []) (resolve f.module result) rfl

theorem core_context_entry_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {result : Option NumType} {body : List Instr} {saved : List Val} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals saved ++ .plain (.block (coreType result) body) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ .label result.toList.length [] (expression body) :: rest⟩ := by
  constructor
  · intro move
    let head := Admin.plain (.block (coreType result) body)
    have first : fnv (vals saved ++ head :: rest) = (saved, head :: rest) := by
      simp [head, fnv_cons_of_none (a := head) rfl]
    rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp move with h | bubble
    · obtain ⟨kept, args, op, tail, next, eq, _, step, rfl⟩ := fnv_headDec h
      rw [first] at eq
      obtain ⟨shape, same⟩ := Prod.mk.inj eq
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      obtain ⟨rfl, rfl⟩ := head_block step
      simp [shape]
    · obtain ⟨_, _, _, _, _, ⟨eq, _, _⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble <;>
        rw [first] at eq <;> simp [head] at eq
  · rintro rfl
    simpa only [List.append_assoc, List.singleton_append] using
      Sim.Step.vals_left (Sim.Step.append_right (core_entry_iff.mpr rfl) rest) saved

private theorem head_label {H : Type} {P : Profile} {s : Store H} {m : ModuleInst}
    {result : Option NumType} {a : Locals.State} {b : Config H}
    (head : Head P s ⟨a.locals.map Locals.coreLocal, m⟩ []
      (.label result.toList.length [] (Locals.coreCodec.encode a.code)) b) :
    ∃ out, Edge (.label result a) out ∧ b = coreConfig s m out := by
  have supported := Locals.coreCodec.supports_encode a.code
  generalize codeEq : Locals.coreCodec.encode a.code = body at head
  cases head with
  | ctxtLabel step =>
    rw [← codeEq] at step
    obtain ⟨out, inner, exactTarget⟩ := Locals.core_step_iff.mp step
    exact ⟨.label result out, reduce result inner,
      congrArg (fun c : Config H => (⟨c.store, c.frame, [.label result.toList.length [] c.code]⟩ : Config H)) exactTarget⟩
  | labelVals eq =>
    have eq := codeEq.trans eq
    have numeric {v : Val} (h : (Locals.coreCodec.read v.toAdmin).isSome) :
        ∃ w : Value, LegacyDivision.liftValue w = v := by
      cases v with
      | num n => exact ⟨⟨n.type, n.bits⟩, by cases n; rfl⟩
      | vec | ref => contradiction
    have numericList (vs : List Val) (h : Locals.coreCodec.Supported (vals vs)) :
        ∃ ws : List Value, ws.map LegacyDivision.liftValue = vs := by
      induction vs with
      | nil => exact ⟨[], rfl⟩
      | cons v vs ih =>
        obtain ⟨hv, tail⟩ := Locals.coreCodec.supports_cons.mp h
        obtain ⟨w, rfl⟩ := numeric hv
        obtain ⟨ws, rfl⟩ := ih tail
        exact ⟨w :: ws, rfl⟩
    rw [eq] at supported
    obtain ⟨vs, rfl⟩ := numericList _ supported
    rw [← encode_values] at eq
    have code := congrArg Locals.coreCodec.decode eq
    simp only [Locals.Codec.decode_encode] at code
    have same : a = ⟨a.locals, Locals.values vs⟩ := by cases a; simp_all
    rw [same]
    exact ⟨.done a.locals vs, exit result a.locals vs, rfl⟩
  | @returnCallRefLabel _ _ _ _ vs c tail eq kind =>
    rw [codeEq, eq] at supported
    have h := (Locals.coreCodec.supports_cons.mp
      (Locals.coreCodec.supports_append.mp (Locals.coreCodec.supports_append.mp supported).1).2).1
    cases read : Locals.coreCodec.read c with
    | none => simp [read] at h
    | some op =>
      have emit := Locals.coreCodec.emit_read read
      subst c
      cases op with
      | value v => rcases v with ⟨t, bits⟩; cases t <;> contradiction
      | _ => contradiction
  | _ =>
    first
    | have hf := (famOf_of_shape (ParametricStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (NumericStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (VectorStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (VariableStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (TableStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (MemoryStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (RefStep.shape ‹_›)).2; contradiction
    | have hf := (famOf_of_shape (AggregateStep.shape ‹_›)).2; contradiction
    | have impossible : (Admin.label result.toList.length [] body).IsCallRef := ‹_›
      exact False.elim impossible
    | rw [codeEq] at supported
      try rw [‹body = _›] at supported
      simp only [Locals.Codec.supports_append, Locals.Codec.supports_cons, Locals.coreCodec,
        Locals.readInstr, Option.isSome_none, Bool.false_eq_true, and_false, false_and] at supported

theorem core_readback {H : Type} {P : Profile} {s : Store H} {m : ModuleInst}
    {a : State} {b : Config H} (step : Step P noHost (coreConfig s m a) b) :
    ∃ out, Edge a out ∧ b = coreConfig s m out := by
  cases a with
  | block result a =>
    refine ⟨.label result a, enter result a, ?_⟩
    simpa only [coreConfig, encode_body] using core_entry_iff.mp step
  | label result a =>
    exact head_label (singleton_head step rfl (by intro h; cases h) (by intro h; cases h))
  | done ls vs => exact (not_step_vals step).elim

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs
