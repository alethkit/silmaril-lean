module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.CallContinuation.Core
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.SingleThreaded.Determinism.Stuck
import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.Core

open Execution.Core Wasm.SingleThreaded.Det
open Execution.Runtime (Value FuncAddr)
open Wasm.Numerics (Profile intBinOp)
open Wasm.Validation (Expand Ty)

private abbrev num (t : IntType) (x : BitVec t.width) : Val := .num ⟨.int t, x⟩
private abbrev get (i : LocalIdx) : Admin := .plain (.localGet i)
private abbrev bin (t : IntType) (op : IntBinOp) : Admin := .plain (.intBinOp t op)
private abbrev call (i : FuncIdx) : Admin := .plain (.call i)
private abbrev nop : Admin := .plain .nop

private theorem core_local {site : Site} {i : LocalIdx} {v : Value}
    (found : site.frame.locals[i.toNat]? = some v) :
    site.frame.toCore.local? i = some (some v.toCore) := by
  change (site.frame.locals.map (fun x : Value => some x.toCore))[i.toNat]? = _
  simp [found]

theorem core_func {m : Execution.Runtime.ModuleInst} {i : FuncIdx} {a : FuncAddr}
    (found : m.funcs[i.toNat]? = some a) : m.toCore.funcs[i.toNat]? = some a.value := by
  change (m.funcs.map (fun x : FuncAddr => x.value))[i.toNat]? = _
  simp [found]

private theorem frame_init (site : Site) :
    Frame.forCall site.outerModule.toCore (site.args.map Value.toCore) site.coreFunc.locals = site.frame.toCore := by
  simp only [Frame.forCall, Site.coreFunc, Site.frame, Execution.Runtime.Frame.toCore,
    List.map_append, List.map_map]
  congr 2
  change (site.locals.map Wasm.V1.ValType.toCore).map _ = _
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  cases t <;> rfl

private theorem resolve_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {dst : Config H} (g : CoreGuard s caller site) :
    Step P noHost (coreConfig s caller site .call) dst ↔ dst = coreConfig s caller site .invoke := by
  have index := core_func g.outerLookup
  constructor
  · intro h
    obtain ⟨a, fi, ha, hf, eq⟩ := Step.call_vals_inv h
    change caller.module.toCore.funcs[site.outerIndex.toNat]? = some a at ha
    rw [index] at ha
    cases ha
    rw [g.outerAlloc] at hf
    cases hf
    exact eq
  · rintro rfl
    exact Sim.Step.vals_left (Step.call index g.outerAlloc) _

private theorem entry_iff {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {dst : Config H} (g : CoreGuard s caller site) :
    Step P noHost (coreConfig s caller site .invoke) dst ↔ dst = coreConfig s caller site .readLeft := by
  have sig : Expand site.type.toDefType (.func (Ty.ofList (site.params.map Ty.num))
      (Ty.ofList (site.inner.result.toList.map Ty.num))) :=
    Expand.iff.mpr (Wasm.V1.FuncType.toDefType_expand _)
  have count : (site.args.map Value.toCore).length = (Ty.ofList (site.params.map Ty.num)).length := by
    simpa [Ty.length_ofList] using congrArg List.length g.typed.outerArgs
  have target : (⟨s, caller.toCore, [.frame (Ty.ofList (site.inner.result.toList.map Ty.num)).length
      (Frame.forCall site.outerModule.toCore (site.args.map Value.toCore) site.coreFunc.locals)
      [.label (Ty.ofList (site.inner.result.toList.map Ty.num)).length [] (expression site.coreFunc.body)]]⟩ :
        Config H) = coreConfig s caller site .readLeft := by
    rw [frame_init, Ty.length_ofList, List.length_map]
    rfl
  constructor
  · intro step
    exact (Step.callRef_wasm_inv_exact (r := .callRefType site.type.toDefType)
      (code := site.coreFunc) (by trivial) g.outerAlloc rfl sig count step).trans target
  · rintro rfl
    rw [← target]
    exact .callRefFunc (c := .callRefType site.type.toDefType) trivial g.outerAlloc sig count rfl

theorem call_iff {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {i : FuncIdx} {a : FuncAddr} {fn : FuncInst H} {stack : List Value} {tail : List Admin} {dst : Config H}
    (lookup : f.module.funcs[i.toNat]? = some a) (alloc : s.funcs[a.value]? = some fn) :
    Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.call i) :: tail⟩ dst ↔
      dst = ⟨s, f.toCore, coreValues stack ++ .ref (.func a.value) :: .callRefType fn.type :: tail⟩ := by
  have found : f.toCore.module.funcs[i.toNat]? = some a.value := core_func lookup
  constructor
  · intro h
    obtain ⟨a', fn', atIndex, atAddr, eq⟩ := Step.call_vals_inv_seq h
    rw [found] at atIndex
    cases atIndex
    rw [alloc] at atAddr
    cases atAddr
    exact eq
  · rintro rfl
    exact Sim.Step.vals_left (Sim.Step.append_right (.call found alloc) tail) _

theorem label_stays {n : Nat} {stack : List Val} {head : Admin} {rest out : List Admin}
    (none : head.val? = none) (notBr : ∀ i, head ≠ .plain (.br i))
    (notRet : head ≠ .plain .return_) (notTail : ¬ head.IsReturnCallRef)
    (notThrow : head ≠ .plain .throwRef) (notFinalTrap : head = .trap → stack ≠ [] ∨ rest ≠ [])
    (h : LabelExit n [] (vals stack ++ head :: rest) out) : False := by
  generalize eq : vals stack ++ head :: rest = code at h
  have seen := congrArg (fun c => (fnv c).2) eq
  simp only [fnv_vals_append, fnv_cons_of_none none] at seen
  cases h with
  | vals => simp at seen
  | brZero | brSucc =>
    simp [List.append_assoc, fnv_cons_of_none (a := .plain (.br _)) rfl] at seen
    exact notBr _ seen.1
  | ret =>
    simp [fnv_cons_of_none (a := .plain .return_) rfl] at seen
    exact notRet seen.1
  | returnCall kind =>
    simp [fnv_cons_of_none (Admin.val?_of_isReturnCallRef kind)] at seen
    exact notTail (seen.1 ▸ kind)
  | throw =>
    simp [throwing, fnv_cons_of_none (a := .plain .throwRef) rfl] at seen
    exact notThrow seen.1
  | trap =>
    simp at seen
    have stackEq := congrArg (fun c => (fnv c).1) eq
    simp only [fnv_vals_append, fnv_cons_of_none none, fnv_trap_cons, List.append_nil] at stackEq
    cases notFinalTrap seen.1 with
    | inl nz => exact nz stackEq
    | inr nz => exact nz seen.2

theorem lift_body {H : Type} {P : Profile} {s s' : Store H}
    {caller inner inner' : Frame} {n : Nat} {a b : List Admin}
    (h : Step P noHost ⟨s, inner, a⟩ ⟨s', inner', b⟩) :
    Step P noHost ⟨s, caller, [.frame n inner [.label n [] a]]⟩
      ⟨s', caller, [.frame n inner' [.label n [] b]]⟩ :=
  .ctxtFrame (.ctxtLabel h)

theorem body_step_cases {H : Type} {P : Profile} {s : Store H} {caller inner : Frame}
    {n : Nat} {body : List Admin} {dst : Config H}
    (h : Step P noHost ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst) :
    (∃ mid : Config H, Step P noHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] mid.code]]⟩) ∨
    ∃ out, LabelExit n [] body out ∧ dst = ⟨s, caller, [.frame n inner out]⟩ := by
  rcases Step.frame_inv h with ⟨_, _, _, step, rfl⟩ | ⟨_, bad, _⟩
  · rcases Step.label_inv step with ⟨_, _, _, innerStep, eq⟩ | ⟨_, pop, eq⟩
    · obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj eq
      exact .inl ⟨_, innerStep, rfl⟩
    · cases eq
      exact .inr ⟨_, pop, rfl⟩
  · exact (CallContinuation.Proofs.frame_label_stays bad).elim

theorem read_body {H : Type} {P : Profile} {s : Store H} {caller inner : Frame}
    {n : Nat} {body : List Admin} {dst : Config H}
    (stays : ∀ {out}, LabelExit n [] body out → False)
    (h : Step P noHost ⟨s, caller, [.frame n inner [.label n [] body]]⟩ dst) :
    ∃ mid : Config H, Step P noHost ⟨s, inner, body⟩ mid ∧
      dst = ⟨mid.store, caller, [.frame n mid.frame [.label n [] mid.code]]⟩ := by
  rcases body_step_cases h with body | ⟨_, pop, _⟩
  · exact body
  · exact (stays pop).elim

private theorem front {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {stack : List Val} {op : Admin} {rest : List Admin} {dst : Config H}
    (none : op.val? = none) (notTrap : op ≠ .trap) (notThrow : op ≠ .plain .throwRef)
    (h : Step P noHost ⟨s, f, vals stack ++ op :: rest⟩ dst) :
    ∃ saved args mid, stack = saved ++ args ∧ Head P s f args op mid ∧
      dst = ⟨mid.store, mid.frame, vals saved ++ mid.code ++ rest⟩ := by
  rcases Wasm.SingleThreaded.Det.Step.decomp h with head | bubble
  · obtain ⟨saved, args, op', tail, mid, eq, _, step, rfl⟩ := fnv_headDec head
    simp only [fnv_vals_append, fnv_cons_of_none none, Prod.mk.injEq, List.cons.injEq, List.append_nil] at eq
    obtain ⟨stackEq, rfl, rfl⟩ := eq
    exact ⟨saved, args, mid, stackEq, step, rfl⟩
  · obtain ⟨_, _, _, _, _, ⟨eq, _, _⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble <;>
      simp [fnv_cons_of_none none, notTrap, notThrow] at eq

theorem if_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {saved : List Val} {condition : BitVec 32} {bt : BlockType} {thenBody elseBody : List Instr}
    {rest : List Admin} {dst : Config H} :
    Step P noHost
      ⟨s, f, vals (saved ++ [.num ⟨.int .i32, condition⟩]) ++ .plain (.if_ bt thenBody elseBody) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ .plain (.block bt (if condition = 0 then elseBody else thenBody)) :: rest⟩ := by
  constructor
  · intro move
    obtain ⟨kept, args, mid, split, step, rfl⟩ := front rfl (by simp) (by simp) move
    cases step with
    | ifTrue nonzero =>
      obtain ⟨rfl, equal⟩ := List.append_inj' split rfl
      cases equal
      rw [ite_eq_right nonzero]
      simp
    | ifFalse zero =>
      obtain ⟨rfl, equal⟩ := List.append_inj' split rfl
      cases equal
      rw [ite_eq_left zero]
      simp
    | _ =>
      first
      | have family := (famOf_of_shape (ParametricStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (NumericStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (VectorStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (VariableStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (TableStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (MemoryStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (RefStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (AggregateStep.shape ‹_›)).2; contradiction
      | contradiction
  · rintro rfl
    have source : vals (saved ++ [(.num ⟨.int .i32, condition⟩ : Val)]) ++ Admin.plain (.if_ bt thenBody elseBody) :: rest =
        vals saved ++ ([constI32 condition, Admin.plain (.if_ bt thenBody elseBody)] ++ rest) := by
      rw [vals_append, List.append_assoc]
      rfl
    rw [source]
    by_cases zero : condition = 0
    · rw [ite_eq_left zero]
      subst condition
      simpa only [vals, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
        Sim.Step.vals_left (Sim.Step.append_right (Step.ifFalse (P := P) (host := noHost)
          (s := s) (f := f) (bt := bt) (b₁ := thenBody) (b₂ := elseBody)) rest) saved
    · rw [ite_eq_right zero]
      simpa only [vals, List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append] using
        Sim.Step.vals_left (Sim.Step.append_right (Step.ifTrue (P := P) (host := noHost)
          (s := s) (f := f) (bt := bt) (b₁ := thenBody) (b₂ := elseBody) zero) rest) saved

theorem br_if_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {saved : List Val} {condition : BitVec 32} {depth : LabelIdx}
    {rest : List Admin} {dst : Config H} :
    Step P noHost
      ⟨s, f, vals (saved ++ [.num ⟨.int .i32, condition⟩]) ++ .plain (.brIf depth) :: rest⟩ dst ↔
      dst = ⟨s, f, vals saved ++ (if condition = 0 then [] else [.plain (.br depth)]) ++ rest⟩ := by
  constructor
  · intro move
    obtain ⟨kept, args, mid, split, step, rfl⟩ := front rfl (by simp) (by simp) move
    cases step with
    | brIfTrue nonzero =>
      obtain ⟨rfl, equal⟩ := List.append_inj' split rfl
      cases equal
      rw [ite_eq_right nonzero]
    | brIfFalse zero =>
      obtain ⟨rfl, equal⟩ := List.append_inj' split rfl
      cases equal
      rw [ite_eq_left zero]
    | _ =>
      first
      | have family := (famOf_of_shape (ParametricStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (NumericStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (VectorStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (VariableStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (TableStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (MemoryStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (RefStep.shape ‹_›)).2; contradiction
      | have family := (famOf_of_shape (AggregateStep.shape ‹_›)).2; contradiction
      | contradiction
  · rintro rfl
    have branch : Step P noHost ⟨s, f, [constI32 condition, .plain (.brIf depth)]⟩
        ⟨s, f, if condition = 0 then [] else [.plain (.br depth)]⟩ := by
      by_cases zero : condition = 0
      · rw [ite_eq_left zero]
        subst condition
        exact .brIfFalse
      · rw [ite_eq_right zero]
        exact .brIfTrue zero
    have source : vals (saved ++ [(.num ⟨.int .i32, condition⟩ : Val)]) ++ .plain (.brIf depth) :: rest =
        vals saved ++ ([constI32 condition, .plain (.brIf depth)] ++ rest) := by
      rw [vals_append, List.append_assoc]
      rfl
    rw [source]
    simpa only [List.append_assoc] using Sim.Step.vals_left (Sim.Step.append_right branch rest) saved

theorem unreachable_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {stack : List Val} {rest : List Admin} {dst : Config H} :
    Step P noHost ⟨s, f, vals stack ++ .plain .unreachable :: rest⟩ dst ↔
      dst = ⟨s, f, vals stack ++ .trap :: rest⟩ := by
  constructor
  · intro move
    obtain ⟨saved, args, mid, rfl, step, rfl⟩ := front rfl (by simp) (by simp) move
    obtain ⟨out, pure, rfl⟩ := step.fam_inv (by change Fam.parametric ≠ .control; decide)
    generalize eq : vals args ++ [Admin.plain .unreachable] = code at pure
    have last := congrArg List.getLast? eq
    cases pure with
    | unreachable =>
      have nil : args = [] := by simpa [vals] using congrArg List.length eq
      subst args
      simp [List.append_assoc]
    | _ => simp [List.getLast?_append] at last
  · rintro rfl
    exact Sim.Step.vals_left (Sim.Step.append_right (.parametric .unreachable) rest) stack

theorem set_read {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {index : LocalIdx} {rest : List Admin} {dst : Config H}
    (move : Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.localSet index) :: rest⟩ dst) :
    ∃ saved v next, stack = saved ++ [v] ∧ Locals.Edge ⟨f.locals, [.value v, .set index]⟩ ⟨next, []⟩ ∧
      dst = ⟨s, (⟨next, f.module⟩ : Execution.Runtime.Frame).toCore, coreValues saved ++ rest⟩ := by
  obtain ⟨saved, args, mid, split, head, rfl⟩ := front rfl (by simp) (by simp) move
  have variableStep : VariableStep ⟨s, f.toCore, vals args ++ [.plain (.localSet index)]⟩ mid :=
    head.fam_inv (by change Fam.variable ≠ .control; decide)
  generalize eq : vals args ++ [Admin.plain (.localSet index)] = code at variableStep
  have last := congrArg List.getLast? eq
  cases variableStep with
  | @localSet _ _ i v bound =>
    simp [List.getLast?_append] at last
    subst i
    have one : args = [v] := vals_inj.mp (List.append_cancel_right eq)
    subst args
    obtain ⟨below, operand, rfl, rfl, values⟩ := List.map_eq_append_iff.mp split
    obtain ⟨w, tail, rfl, rfl, empty⟩ := List.map_eq_cons_iff.mp values
    have nil : tail = [] := List.map_eq_nil_iff.mp empty
    subst tail
    have fits : index.toNat < f.locals.length := by simpa [Execution.Runtime.Frame.toCore] using bound
    refine ⟨below, w, _, rfl, Locals.fact (.set _ _ _ fits), ?_⟩
    cases f
    simp [Frame.setLocal, Execution.Runtime.Frame.toCore, List.map_set, coreValues]
  | _ => simp [List.getLast?_append] at last

theorem tee_read {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {index : LocalIdx} {rest : List Admin} {dst : Config H}
    (move : Step P noHost ⟨s, f.toCore, coreValues stack ++ .plain (.localTee index) :: rest⟩ dst) :
    ∃ saved v, stack = saved ++ [v] ∧
      Locals.Edge ⟨f.locals, [.value v, .tee index]⟩ ⟨f.locals, [.value v, .value v, .set index]⟩ ∧
      dst = ⟨s, f.toCore, coreValues (saved ++ [v, v]) ++ .plain (.localSet index) :: rest⟩ := by
  obtain ⟨saved, args, mid, split, head, rfl⟩ := front rfl (by simp) (by simp) move
  have variableStep : VariableStep ⟨s, f.toCore, vals args ++ [.plain (.localTee index)]⟩ mid :=
    head.fam_inv (by change Fam.variable ≠ .control; decide)
  generalize eq : vals args ++ [Admin.plain (.localTee index)] = code at variableStep
  have last := congrArg List.getLast? eq
  cases variableStep with
  | @localTee _ _ i v =>
    simp [List.getLast?_append] at last
    subst i
    have one : args = [v] := vals_inj.mp (List.append_cancel_right eq)
    subst args
    obtain ⟨below, operand, rfl, rfl, values⟩ := List.map_eq_append_iff.mp split
    obtain ⟨w, tail, rfl, rfl, empty⟩ := List.map_eq_cons_iff.mp values
    have nil : tail = [] := List.map_eq_nil_iff.mp empty
    subst tail
    exact ⟨below, w, rfl, Locals.fact (.tee _ _ _), by
      simp [coreValues, List.map_append, vals, List.append_assoc]⟩
  | _ => simp [List.getLast?_append] at last

private theorem get_read {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {stack : List Val} {i : LocalIdx} {rest : List Admin} {dst : Config H}
    (h : Step P noHost ⟨s, f, vals stack ++ get i :: rest⟩ dst) :
    ∃ v, f.local? i = some (some v) ∧ dst = ⟨s, f, vals stack ++ v.toAdmin :: rest⟩ := by
  obtain ⟨saved, args, mid, rfl, step, rfl⟩ := front rfl (by simp) (by simp) h
  have localStep : VariableStep ⟨s, f, vals args ++ [get i]⟩ mid :=
    step.fam_inv (by change Fam.variable ≠ .control; decide)
  generalize eq : vals args ++ [get i] = code at localStep
  have last := congrArg List.getLast? eq
  cases localStep with
  | @localGet _ _ j w found =>
    simp [List.getLast?_append] at last
    subst j
    have empty : args = [] := by simpa [vals] using congrArg List.length eq
    subst args
    exact ⟨w, found, by simp⟩
  | _ => simp [List.getLast?_append] at last

private theorem get_iff {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {stack : List Val} {i : LocalIdx} {v : Val} {rest : List Admin} {dst : Config H}
    (lookup : f.local? i = some (some v)) :
    Step P noHost ⟨s, f, vals stack ++ get i :: rest⟩ dst ↔
      dst = ⟨s, f, vals stack ++ v.toAdmin :: rest⟩ := by
  constructor
  · intro step
    obtain ⟨w, found, eq⟩ := get_read step
    rw [lookup] at found
    cases found
    exact eq
  · rintro rfl
    exact Sim.Step.vals_left (Sim.Step.append_right (.variable (.localGet lookup)) rest) stack

private theorem bin_read {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {t : IntType} {op : IntBinOp} {stack : List Val} {rest : List Admin} {dst : Config H}
    (h : Step P noHost ⟨s, f, vals stack ++ bin t op :: rest⟩ dst) :
    ∃ (saved : List Val) (x y : BitVec t.width), stack = saved ++ [num t x, num t y] ∧
      ((∃ z, intBinOp t op x y = .ok z ∧ dst = ⟨s, f, vals saved ++ (num t z).toAdmin :: rest⟩) ∨
      (∃ e, intBinOp t op x y = .error e ∧ dst = ⟨s, f, vals saved ++ .trap :: rest⟩)) := by
  obtain ⟨saved, args, mid, total, step, rfl⟩ := front rfl (by simp) (by simp) h
  obtain ⟨out, numeric, rfl⟩ := step.fam_inv (by change Fam.numeric ≠ .control; decide)
  generalize eq : vals args ++ [bin t op] = code at numeric
  have last := congrArg List.getLast? eq
  cases numeric with
  | @intBinOp u o a b z hz =>
    simp [List.getLast?_append] at last
    obtain ⟨rfl, rfl⟩ := last
    have argsEq : args = [num t a, num t b] := vals_inj.mp (List.append_cancel_right eq)
    subst args
    exact ⟨saved, a, b, total, .inl ⟨z, hz, by rw [List.append_assoc]; rfl⟩⟩
  | @intBinOpTrap u o a b e he =>
    simp [List.getLast?_append] at last
    obtain ⟨rfl, rfl⟩ := last
    have argsEq : args = [num t a, num t b] := vals_inj.mp (List.append_cancel_right eq)
    subst args
    exact ⟨saved, a, b, total, .inr ⟨e, he, by simp⟩⟩
  | _ => simp [List.getLast?_append] at last

private theorem bin_step {H : Type} {P : Profile} {s : Store H} {f : Frame}
    {t : IntType} {op : IntBinOp} {x y : BitVec t.width} {rest : List Admin} {dst : Config H}
    (h : Step P noHost ⟨s, f, vals [num t x, num t y] ++ bin t op :: rest⟩ dst) :
    (∃ z, intBinOp t op x y = .ok z ∧ dst = ⟨s, f, (num t z).toAdmin :: rest⟩) ∨
    (∃ e, intBinOp t op x y = .error e ∧ dst = ⟨s, f, .trap :: rest⟩) := by
  obtain ⟨saved, a, b, total, out⟩ := bin_read h
  obtain ⟨rfl, left, right⟩ := two_values total
  have hx : x = a := eq_of_heq (NumVal.mk.inj (Val.num.inj left)).2
  have hy : y = b := eq_of_heq (NumVal.mk.inj (Val.num.inj right)).2
  subst a b
  exact out

private theorem int_value {v : Value} {t : IntType} {x : BitVec t.width}
    (eq : v.toCore = num t x) : v = .int t x := by
  cases v
  cases Val.num.inj eq
  rfl

@[local simp] private theorem int_admin (t : IntType) (bits : BitVec t.width) :
    (Value.int t bits).toCore.toAdmin = .plain (.intConst t bits) := rfl

@[local simp] private theorem num_admin (t : IntType) (bits : BitVec t.width) :
    (num t bits).toAdmin = .plain (.intConst t bits) := rfl

theorem prefix_read {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {op : Prefix.Op} {suffix : List Admin} {dst : Config H}
    (step : Step P noHost ⟨s, f.toCore, coreValues stack ++ Prefix.emit coreSyntax op :: suffix⟩ dst) :
    ∃ ans, Prefix.Reduce f.locals stack op ans ∧
      dst = ⟨s, f.toCore, Prefix.outcomeCode coreValues .trap suffix ans⟩ := by
  cases op with
  | get i =>
    obtain ⟨v, found, eq⟩ := get_read step
    change (f.locals.map (fun w : Value => some w.toCore))[i.toNat]? = some (some v) at found
    rw [List.getElem?_map] at found
    cases lookup : f.locals[i.toNat]? with
    | none => simp [lookup] at found
    | some w =>
      simp only [lookup, Option.map_some, Option.some.injEq] at found
      subst v
      exact ⟨_, .get lookup, by simpa [Prefix.outcomeCode, coreValues, List.map_append, vals_append, List.append_assoc, vals] using eq⟩
  | bin t op =>
    obtain ⟨saved, x, y, split, ans⟩ := bin_read step
    obtain ⟨kept, operands, rfl, rfl, written⟩ := List.map_eq_append_iff.mp split
    obtain ⟨a, rest, rfl, left, written⟩ := List.map_eq_cons_iff.mp written
    obtain ⟨b, tail, rfl, right, written⟩ := List.map_eq_cons_iff.mp written
    have nil : tail = [] := List.map_eq_nil_iff.mp written
    subst tail
    rw [int_value left, int_value right]
    rcases ans with ⟨z, ok, eq⟩ | ⟨_, err, eq⟩
    · exact ⟨_, .bin ok, by
        simpa [Prefix.outcomeCode, coreValues, List.map_append, vals_append, List.append_assoc, vals] using eq⟩
    · exact ⟨_, .trap err, eq⟩

theorem prefix_sound {H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    {stack : List Value} {op : Prefix.Op} {suffix : List Admin} {ans : Prefix.Outcome}
    (step : Prefix.Reduce f.locals stack op ans) :
    Step P noHost ⟨s, f.toCore, coreValues stack ++ Prefix.emit coreSyntax op :: suffix⟩
      ⟨s, f.toCore, Prefix.outcomeCode coreValues .trap suffix ans⟩ := by
  cases step with
  | @get stack i v found =>
    have lookup : f.toCore.local? i = some (some v.toCore) := by
      change (f.locals.map (fun w : Value => some w.toCore))[i.toNat]? = _
      simp [found]
    simpa [Prefix.outcomeCode, Prefix.emit, coreSyntax, coreValues, List.map_append, vals_append, List.append_assoc, vals] using
      (get_iff (s := s) (P := P) (stack := stack.map Value.toCore) (rest := suffix) lookup).mpr rfl
  | @bin saved t oper x y z ok =>
    simpa [Prefix.outcomeCode, Prefix.emit, coreSyntax, coreValues, List.map_append, vals_append, List.append_assoc, vals] using
      Sim.Step.vals_left (Sim.Step.append_right (Step.numeric (s := s) (P := P) (host := noHost) (f := f.toCore)
        (NumericStep.intBinOp ok)) suffix) (saved.map Value.toCore)
  | @trap saved t oper x y cause err =>
    simpa [Prefix.outcomeCode, Prefix.emit, coreSyntax, coreValues, List.map_append, vals_append, List.append_assoc, vals] using
      Sim.Step.vals_left (Sim.Step.append_right (Step.numeric (s := s) (P := P) (host := noHost) (f := f.toCore)
        (NumericStep.intBinOpTrap err)) suffix) (saved.map Value.toCore)

theorem prefix_discard_read {A H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    (emit : A → Admin) {stack : List Value} {tail : List A} {dst : Config H}
    (step : Step P noHost ⟨s, f.toCore, coreValues stack ++ .trap :: tail.map emit⟩ dst) :
    ∃ kept rest, Prefix.Discard stack tail kept rest ∧
      dst = ⟨s, f.toCore, coreValues kept ++ .trap :: rest.map emit⟩ := by
  rcases Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨_, _, _, _, _, eq, _, h, _⟩ := fnv_headDec head
    simp at eq
    exact (h.good.ne_trap eq.2.1.symm).elim
  · obtain ⟨kept, removed, cut, rest, nz, ⟨eq, _, rfl⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble
    · simp only [fnv_vals_append, fnv_trap_cons, List.append_nil, Prod.mk.injEq, List.cons.injEq, true_and] at eq
      obtain ⟨left, right⟩ := eq
      obtain ⟨a, b, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp left
      obtain ⟨c, d, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp right
      exact ⟨a, d, .cut a b c d (by simpa using nz), by simp⟩
    · simp at eq

theorem prefix_discard_sound {A H : Type} {P : Profile} {s : Store H} {f : Execution.Runtime.Frame}
    (emit : A → Admin) {stack kept : List Value} {tail rest : List A}
    (step : Prefix.Discard stack tail kept rest) :
    Step P noHost ⟨s, f.toCore, coreValues stack ++ .trap :: tail.map emit⟩
      ⟨s, f.toCore, coreValues kept ++ .trap :: rest.map emit⟩ := by
  cases step with
  | cut kept removed cut rest nz =>
    have trap := Step.trapInstrs (P := P) (host := noHost) (s := s) (f := f.toCore)
      (vs := removed.map Value.toCore) (rest := cut.map emit) (by simpa using nz)
    simpa [coreValues, List.map_append, vals_append, List.append_assoc] using
      Sim.Step.vals_left (Sim.Step.append_right trap (rest.map emit)) (kept.map Value.toCore)

private theorem trap_step {H : Type} {P : Profile} {s : Store H} {f : Frame} {i : FuncIdx}
    {dst : Config H} (h : Step P noHost ⟨s, f, [.trap, call i, nop]⟩ dst) :
    dst = ⟨s, f, [.trap, nop]⟩ ∨ dst = ⟨s, f, [.trap]⟩ := by
  rcases Wasm.SingleThreaded.Det.Step.decomp h with head | bubble
  · obtain ⟨_, _, _, _, _, eq, _, step, _⟩ := fnv_headDec head
    simp at eq
    exact (step.good.ne_trap eq.2.1.symm).elim
  · obtain ⟨kept, removed, cut, rest, ne, ⟨eq, _, rfl⟩ | ⟨_, eq, _, _⟩⟩ := fnv_bubble bubble
    · simp at eq
      obtain ⟨⟨rfl, rfl⟩, split⟩ := eq
      cases cut with
      | nil => cases ne <;> contradiction
      | cons hd cut =>
        simp at split
        obtain ⟨rfl, split⟩ := split
        cases cut with
        | nil => exact .inl (by simpa using congrArg (fun xs => (⟨s, f, .trap :: xs⟩ : Config H)) split.symm)
        | cons hd cut =>
          simp at split
          obtain ⟨rfl, rfl, rfl⟩ := split
          exact .inr rfl
    · simp at eq

private theorem resolve_inner_iff {H : Type} {P : Profile} {s : Store H}
    {site : Site} {caller : Execution.Runtime.Frame} {dst : Config H} {z : BitVec site.kind.width}
    (g : CoreGuard s caller site) :
    Step P noHost ⟨s, site.frame.toCore, vals [num site.kind z] ++ [call site.innerIndex, nop]⟩ dst ↔
      dst = ⟨s, site.frame.toCore, vals [num site.kind z] ++
        [.ref (.func site.innerAddr.value), .callRefType site.inner.type.toDefType, nop]⟩ := by
  have index := core_func g.innerLookup
  constructor
  · intro h
    obtain ⟨a, inst, lookup, alloc, eq⟩ := Step.call_vals_inv_seq h
    change site.outerModule.toCore.funcs[site.innerIndex.toNat]? = some a at lookup
    rw [index] at lookup
    cases lookup
    rw [g.innerAlloc] at alloc
    cases alloc
    exact eq
  · rintro rfl
    exact Sim.Step.vals_left (Sim.Step.append_right (Step.call index g.innerAlloc) [nop]) _

theorem sound {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a b : State site} (g : CoreGuard s caller site) (edge : Edge site a b) :
    Step P noHost (coreConfig s caller site a) (coreConfig s caller site b) := by
  cases invert edge with
  | nest h => exact Nested.core_sound g.innerAlloc h
  | ground rule =>
    cases rule with
    | resolve => exact (resolve_iff g).mpr rfl
    | enter => exact (entry_iff g).mpr rfl
    | readLeft =>
      exact lift_body ((get_iff (stack := []) (core_local g.typed.leftLookup)).mpr rfl)
    | readRight =>
      exact lift_body ((get_iff (stack := [num site.kind site.left]) (core_local g.typed.rightLookup)).mpr rfl)
    | compute ok =>
      exact lift_body (Sim.Step.append_right (.numeric (.intBinOp ok)) _)
    | trap err =>
      exact lift_body (Sim.Step.append_right (.numeric (.intBinOpTrap err)) _)
    | dropCall =>
      exact lift_body (Sim.Step.append_right (Step.trapInstrs (vs := []) (rest := [call site.innerIndex])
        (.inr (List.cons_ne_nil _ _))) [nop])
    | dropCallAndNop =>
      exact lift_body (Step.trapInstrs (vs := []) (rest := [call site.innerIndex, nop]) (.inr (List.cons_ne_nil _ _)))
    | resolveInner z => exact lift_body ((resolve_inner_iff g (z := z)).mpr rfl)

theorem readback {H : Type} {P : Profile} {s : Store H} {caller : Execution.Runtime.Frame}
    {site : Site} {a : State site} {dst : Config H} (g : CoreGuard s caller site) (ready : Admitted site a)
    (h : Step P noHost (coreConfig s caller site a) dst) :
    ∃ out, Edge site a out ∧ dst = coreConfig s caller site out := by
  cases a with
  | call => exact ⟨.invoke, fact .resolve, (resolve_iff g).mp h⟩
  | invoke => exact ⟨.readLeft, fact .enter, (entry_iff g).mp h⟩
  | nested q =>
    obtain ⟨out, edge, eq⟩ := (Nested.core_step_iff g.innerAlloc ready).mp h
    exact ⟨.nested out, delegate edge, eq⟩
  | readLeft =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := []) (head := get site.leftIndex) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp [Site.suffix])) h
    have read := (get_iff (stack := []) (core_local g.typed.leftLookup)).mp move
    exact ⟨.readRight, fact .readLeft, eq.trans (by rw [read]; rfl)⟩
  | readRight =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [num site.kind site.left]) (head := get site.rightIndex) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp [Site.suffix])) h
    have read := (get_iff (stack := [num site.kind site.left]) (core_local g.typed.rightLookup)).mp move
    exact ⟨.compute, fact .readRight, eq.trans (by rw [read]; rfl)⟩
  | compute =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [num site.kind site.left, num site.kind site.right])
        (head := bin site.kind site.op) rfl (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp [Site.suffix])) h
    rcases bin_step move with ⟨z, ok, rfl⟩ | ⟨_, err, rfl⟩
    · exact ⟨.argument z, fact (.compute ok), eq⟩
    · exact ⟨.argumentTrap, fact (.trap err), eq⟩
  | argument z =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := [num site.kind z]) (head := call site.innerIndex) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp)) h
    exact ⟨.nested (site.innerStart z), fact (.resolveInner z),
      eq.trans (by rw [(resolve_inner_iff g (z := z)).mp move]; rfl)⟩
  | argumentTrap =>
    obtain ⟨mid, move, eq⟩ := read_body
      (label_stays (stack := []) (head := .trap) rfl
        (by simp) (by simp) (by simp [Admin.IsReturnCallRef]) (by simp) (by simp [Site.suffix])) h
    rcases trap_step move with rfl | rfl
    · exact ⟨_, fact .dropCall, eq⟩
    · exact ⟨_, fact .dropCallAndNop, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Proofs.Core
