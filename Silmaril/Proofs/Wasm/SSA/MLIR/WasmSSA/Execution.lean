module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Execution.Defs
import Silmaril.Wasm.Logic.Core.Thms

/-! Core runs of the erased, intrinsically typed lowering. -/

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.MLIR.WasmSSA.Lowering
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Validation (Context Expand Ty)
open Silmaril.Wasm (Instr LocalIdx TypeIdx)

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {fr : Frame}

/-- Each available source word is stored below the next fresh local. -/
private def Reads {C : Context} {ts : List IntType} (fr : Frame) (next : Nat)
    (slots : Slots C ts) (env : Env ts) : Prop :=
  ∀ {t} (ref : Ref ts t), (slots ref).index.toNat < next ∧
    fr.local? (slots ref).index = some (some (t.toVal (env.get ref)))

private theorem Reads.advance {C : Context} {ts : List IntType} {next : Nat}
    {slots : Slots C ts} {env : Env ts} {idx : LocalIdx} {word : Val}
    (h : Reads fr next slots env) (fresh : idx.toNat = next) :
    Reads (fr.setLocal idx word) (next + 1) slots env := by
  intro t ref
  obtain ⟨before, read⟩ := h ref
  change (slots ref).index.toNat < next at before
  refine ⟨Nat.lt_succ_of_lt before, ?_⟩
  have different : idx.toNat ≠ (slots ref).index.toNat :=
    Nat.ne_of_gt (fresh.symm ▸ before)
  simpa only [Frame.local?, Frame.setLocal, List.getElem?_set_ne different] using read

private theorem Reads.cons {C : Context} {ts : List IntType} {t : IntType} {next : Nat}
    {slots : Slots C ts} {env : Env ts} (slot : Slot C t) (word : BitVec t.width)
    (h : Reads fr next slots env) (fresh : slot.index.toNat = next)
    (inBounds : next < fr.locals.length) :
    Reads (fr.setLocal slot.index (t.toVal word)) (next + 1)
      (Slots.cons slot slots) (.cons word env) := by
  intro ty ref
  cases ref with
  | here =>
    refine ⟨by simp [Slots.cons, fresh], ?_⟩
    have indexBound : slot.index.toNat < fr.locals.length := fresh ▸ inBounds
    simp [Slots.cons, Env.get, Frame.local?, Frame.setLocal, indexBound]
  | there ref => exact (h.advance fresh) ref

private theorem localGet_steps {idx : LocalIdx} {v : Val}
    (read : fr.local? idx = some (some v)) (stack : List Val) (rest : List Admin) :
    Steps P host ⟨s, fr, vals stack ++ .plain (.localGet idx) :: rest⟩
      ⟨s, fr, vals stack ++ v.toAdmin :: rest⟩ := by
  apply Relation.ReflTransGen.single
  simpa only [List.append_assoc, List.singleton_append] using
    (Step.ctx (P := P) (host := host) stack rest (.variable (.localGet (s := s) read)))

private theorem readPair_steps {C : Context} {t : IntType} {lhs rhs : Slot C t} {x y : Val}
    (left : fr.local? lhs.index = some (some x)) (right : fr.local? rhs.index = some (some y))
    (rest : List Admin) :
    Steps P host ⟨s, fr, .plain (.localGet lhs.index) :: .plain (.localGet rhs.index) :: rest⟩
      ⟨s, fr, x.toAdmin :: y.toAdmin :: rest⟩ :=
  (localGet_steps left [] (.plain (.localGet rhs.index) :: rest)).trans
    (localGet_steps right [x] rest)

private theorem toVal_toAdmin (t : IntType) (word : BitVec t.width) :
    (t.toVal word).toAdmin = .plain (.intConst t.toWasm (t.width_toWasm.symm ▸ word)) := by
  cases t <;> rfl

private theorem lowerOp_steps {C : Context} {params Γ : List IntType} {t : IntType}
    (rhs : Rhs params Γ t) {paramsAt : Slots C params} {valsAt : Slots C Γ}
    {args : Env params} {values : Env Γ} {next : Nat}
    (paramsRead : Reads fr next paramsAt args) (valuesRead : Reads fr next valsAt values) :
    Steps P host ⟨s, fr, expression (lowerOp paramsAt valsAt rhs).erase⟩
      ⟨s, fr, vals [t.toVal (rhs.eval args values)]⟩ := by
  cases rhs with
  | const word =>
    change Steps P host ⟨s, fr, [.plain (.intConst t.toWasm (t.width_toWasm.symm ▸ word))]⟩
      ⟨s, fr, [(t.toVal word).toAdmin]⟩
    rw [toVal_toAdmin]
  | localGet ref => exact localGet_steps (paramsRead ref).2 [] []
  | binary op lhs rhs =>
    refine (readPair_steps (valuesRead lhs).2 (valuesRead rhs).2
      [.plain (.intBinOp t.toWasm op.toWasm)]).trans (.single (.numeric ?_))
    cases t <;> cases op <;> exact NumericStep.intBinOp rfl
  | eqz input =>
    refine (localGet_steps (valuesRead input).2 []
      [.plain (.intTestOp _ .eqz)]).trans (.single (.numeric ?_))
    cases ‹IntType› <;> exact NumericStep.intTestOp
  | lt sign lhs rhs =>
    refine (readPair_steps (valuesRead lhs).2 (valuesRead rhs).2
      [.plain (.intRelOp _ (.lt sign.toWasm))]).trans (.single (.numeric ?_))
    cases ‹IntType› <;> cases sign <;> exact NumericStep.intRelOp
  | select condition ifTrue ifFalse =>
    let ts := some [t.valType]
    refine (readPair_steps (valuesRead ifTrue).2 (valuesRead ifFalse).2
      [.plain (.localGet (valsAt condition).index), .plain (.select ts)]).trans ?_
    refine (localGet_steps (valuesRead condition).2
      [t.toVal (values.get ifTrue), t.toVal (values.get ifFalse)] [.plain (.select ts)]).trans ?_
    by_cases zero : values.get condition = 0
    · simp only [vals, List.map_cons, List.map_nil, Rhs.eval, zero, ↓reduceIte]
      exact .single (.parametric (.selectFalse _ _ ts))
    · simp only [vals, List.map_cons, List.map_nil, Rhs.eval, zero, ↓reduceIte]
      exact .single (.parametric (.selectTrue zero))

private theorem lowerBlock_returns {C : Context} {params Γ : List IntType} {result : IntType}
    (b : Block params result Γ) (paramsAt : Slots C params) (valsAt : Slots C Γ)
    (next : Nat) (layout : C.locals.drop next = b.bindingTypes.map IntType.localType)
    (fits : C.locals.length ≤ 2 ^ 32) (returns : C.return_ = some [result.closed])
    (args : Env params) (values : Env Γ) (size : fr.locals.length = C.locals.length)
    (paramsRead : Reads fr next paramsAt args) (valuesRead : Reads fr next valsAt values) :
    ∃ final, Steps P host ⟨s, fr, expression (lowerBlock b paramsAt valsAt next layout fits returns).erase⟩
      ⟨s, final, vals [result.toVal (Block.eval args values b)] ++ [.plain .return_]⟩ := by
  induction b generalizing fr next with
  | return_ ref => exact ⟨fr, localGet_steps (valuesRead ref).2 [] [.plain .return_]⟩
  | letOp rhs rest ih =>
    rename_i Γ t
    let slot := bindingSlot (t := t) next layout fits
    let word := rhs.eval args values
    let fr' := fr.setLocal slot.index (t.toVal word)
    have inBounds : next < fr.locals.length := by
      rw [size]
      exact (List.getElem?_eq_some_iff.mp slot.resolves).choose
    have restLayout : C.locals.drop (next + 1) = rest.bindingTypes.map IntType.localType := by
      rw [← List.drop_drop, layout]
      rfl
    obtain ⟨final, runRest⟩ := ih (Slots.cons slot valsAt) (next + 1) restLayout (.cons word values)
      (fr := fr') (by simpa [fr', Frame.setLocal] using size)
      (paramsRead.advance rfl) (valuesRead.cons slot word rfl inBounds)
    let suffix := expression (lowerBlock rest paramsAt (Slots.cons slot valsAt)
      (next + 1) restLayout fits returns).erase
    refine ⟨final, ?_⟩
    have runRhs := Steps.append (.plain (.localSet slot.index) :: suffix)
      (lowerOp_steps (P := P) (host := host) (s := s) rhs paramsRead valuesRead)
    have setSlot : Step P host ⟨s, fr, [(t.toVal word).toAdmin, .plain (.localSet slot.index)]⟩
        ⟨s, fr', []⟩ := .variable (.localSet inBounds)
    have runSet : Steps P host _ _ := .single setSlot
    have run := runRhs.trans ((Steps.append suffix runSet).trans runRest)
    simp only [lowerBlock, thenBody, store, Silmaril.Wasm.Validation.Intrinsic.Body.erase,
      Silmaril.Wasm.Validation.Intrinsic.Step.erase, expression, List.map_append, List.map_cons,
      List.singleton_append, Block.eval]
    exact run

private theorem toWasmArgs_length {ts : List IntType} (args : Env ts) :
    args.toWasmArgs.length = ts.length := by
  induction args with
  | nil => rfl
  | cons _ _ ih => simp [Env.toWasmArgs, ih]

private theorem toWasmArgs_get {ts : List IntType} {t : IntType} (args : Env ts) (ref : Ref ts t) :
    args.toWasmArgs[ref.index]? = some (t.toVal (args.get ref)) := by
  induction ref with
  | here => cases args; rfl
  | there _ ih => cases args; exact ih _

theorem toWasm_returns {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params) (m : ModuleInst)
    (P : Profile) (host : HostSemantics H) (s : Store H) :
    ∃ final, Steps P host
      ⟨s, Frame.forCall m args.toWasmArgs (f.toWasm C type fits).locals,
        expression (f.toWasm C type fits).body⟩
      ⟨s, final, vals [result.toVal (f.eval args)] ++ [.plain .return_]⟩ := by
  unfold Func.toWasm Func.toBody Func.eval
  apply lowerBlock_returns
  · simp [Frame.forCall, toWasmArgs_length, Func.bodyContext, Func.paramTypes, Context.funcBody]
  · intro t ref
    have before := (List.getElem?_eq_some_iff.mp ref.getElem?_index).choose
    refine ⟨before, ?_⟩
    change ((args.toWasmArgs.map some ++ _)[ref.index]?) = some (some (t.toVal (args.get ref)))
    rw [List.getElem?_append_left (by simpa [toWasmArgs_length] using before)]
    simp [toWasmArgs_get]
  · intro t ref
    nomatch ref

theorem toWasm_invoke {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) (args : Env params)
    (P : Profile) (host : HostSemantics H) (s : Store H) (addr : Nat) (fi : FuncInst H)
    (lookup : s.funcs[addr]? = some fi) (code : fi.code = .wasm (f.toWasm C type fits))
    (signature : Expand fi.type (Func.coreSignature params result)) :
    Steps P host (invoke s addr args.toWasmArgs) ⟨s, {}, vals [result.toVal (f.eval args)]⟩ := by
  obtain ⟨s', res, run, hs, hr⟩ := funcSpec_invoke_of_body
    (Pre := fun store inputs => store = s ∧ inputs = args.toWasmArgs)
    (Post := fun _ _ store outputs => store = s ∧ outputs = [result.toVal (f.eval args)])
    (fun _ _ h => h.1.symm ▸ lookup) code signature
    (fun _ _ h => by simpa [h.2, Ty.length_ofList, Func.paramTypes] using toWasmArgs_length args)
    (fun store inputs h => by
      rcases h with ⟨rfl, rfl⟩
      obtain ⟨_, run⟩ := toWasm_returns f C type fits args fi.module P host store
      exact WP.steps run (wp_return ⟨[], [result.toVal (f.eval args)], rfl, rfl, rfl, rfl⟩))
    (s := s) (args := args.toWasmArgs) (P := P) (host := host) ⟨rfl, rfl⟩
  simpa only [hs, hr] using run

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA
