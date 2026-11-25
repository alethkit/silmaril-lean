module

public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
import Silmaril.Wasm.Execution.Core.Inversion.Thms

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

theorem core_block_step_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {bt : BlockType} {body : List Instr} {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals stack ++ .plain (.block bt body) :: rest⟩ dst ↔
      ∃ (saved args : List Val) (params results : List Wasm.Validation.CValType),
        stack = saved ++ args ∧ f.module.blockType? bt = some (params, results) ∧
        args.length = params.length ∧
        dst = ⟨s, f, vals saved ++ .label results.length [] (vals args ++ expression body) :: rest⟩ := by
  constructor
  · rcases dst with ⟨s', f', code⟩
    intro step
    rcases Sim.Step.split_head (a := .plain (.block bt body)) rfl step with
      ⟨outside, used, _, split, head, rfl⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
    · obtain ⟨kept, args, params, results, eq, lookup, count, target⟩ := head.block_vals_inv
      cases target
      exact ⟨outside ++ kept, args, params, results, by rw [split, eq, List.append_assoc],
        lookup, count, by simp only [vals_append, List.append_assoc, List.singleton_append]⟩
    · cases bad
    · cases bad
  · rintro ⟨saved, args, params, results, rfl, lookup, count, rfl⟩
    simpa only [vals_append, List.append_assoc, List.singleton_append] using
      Sim.Step.vals_left (Sim.Step.append_right (Step.block (P := P) (host := noHost) (s := s)
        (body := body) lookup count) rest) saved

theorem core_locals_label_exit {n : Nat} {ops : List Locals.Op} {out : List Admin}
    (pop : LabelExit n [] (Locals.coreCodec.encode ops) out) :
    ∃ vs, ops = Locals.values vs ∧ out = vals (vs.map LegacyDivision.liftValue) := by
  have supported := Locals.coreCodec.supports_encode ops
  generalize eq : Locals.coreCodec.encode ops = body at pop
  cases pop with
  | vals vs =>
    have numericList (vs : List Val) (ok : Locals.coreCodec.Supported (vals vs)) :
        ∃ values : List Value, values.map LegacyDivision.liftValue = vs := by
      induction vs with
      | nil => exact ⟨[], rfl⟩
      | cons v vs ih =>
        obtain ⟨head, tail⟩ := Locals.coreCodec.supports_cons.mp ok
        obtain ⟨values, rfl⟩ := ih tail
        cases v with
        | num v => exact ⟨⟨v.type, v.bits⟩ :: values, by cases v; rfl⟩
        | vec | ref => contradiction
    rw [eq] at supported
    obtain ⟨values, rfl⟩ := numericList vs supported
    rw [← encode_values] at eq
    exact ⟨values, by simpa using congrArg Locals.coreCodec.decode eq, rfl⟩
  | returnCall kind =>
    rw [eq] at supported
    rename_i vs op rest
    have read := supported op (by simp)
    cases found : Locals.coreCodec.read op with
    | none => simp [found] at read
    | some op' =>
      have emit := Locals.coreCodec.emit_read found
      subst op
      cases op' with
      | value v => rcases v with ⟨t, bits⟩; cases t <;> contradiction
      | _ => contradiction
  | _ =>
    rw [eq] at supported
    simp [Locals.coreCodec, Locals.readInstr, throwing] at supported

theorem core_readback {H : Type} {P : Profile} {s : Store H} {m : ModuleInst}
    {a : State} {b : Config H} (step : Step P noHost (coreConfig s m a) b) :
    ∃ out, Edge a out ∧ b = coreConfig s m out := by
  cases a with
  | block result a =>
    refine ⟨.label result a, enter result a, ?_⟩
    simpa only [coreConfig, encode_body] using core_entry_iff.mp step
  | label result a =>
    rcases Step.label_inv step with ⟨s', f', code, inside, rfl⟩ | ⟨out, pop, rfl⟩
    · obtain ⟨next, move, same⟩ := Locals.core_step_iff.mp inside
      exact ⟨.label result next, reduce result move,
        congrArg (fun c : Config H => (⟨c.store, c.frame, [.label result.toList.length [] c.code]⟩ : Config H)) same⟩
    · obtain ⟨vs, code, rfl⟩ := core_locals_label_exit pop
      have eq : a = ⟨a.locals, Locals.values vs⟩ := by cases a; simp_all
      rw [eq]
      exact ⟨.done a.locals vs, exit result a.locals vs, rfl⟩
  | done ls vs => exact (not_step_vals step).elim

end Silmaril.Wasm.Institution.Operational.Blocks.Proofs
