module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Defs
import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context
import Silmaril.Wasm.Validation.Subtyping.Check
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Sequence.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.Core

open Execution.Core
open Execution.Runtime (Value)
open CallContinuation.OuterCall.Ranked.Graph (Program Function)
open Wasm.SingleThreaded.Det (famOf noHost)
open Wasm.Validation

variable {H : Type} {P : Numerics.Profile} {s : Store H}

private theorem one_operand {stack : List Val} {head operand op : Admin}
    (eq : vals stack ++ [head] = [operand, op]) :
    ∃ v, stack = [v] ∧ v.toAdmin = operand ∧ head = op := by
  rcases stack with _ | ⟨v, _ | ⟨w, rest⟩⟩
  · simp [vals] at eq
  · exact ⟨v, rfl, (List.cons.inj eq).1, (List.cons.inj (List.cons.inj eq).2).1⟩
  · simp only [vals, List.map_cons, List.cons_append, List.cons.injEq] at eq
    obtain ⟨_, _, impossible⟩ := eq
    cases rest <;> simp at impossible

private theorem of_value_code {v w : Val} (eq : v.toAdmin = w.toAdmin) : v = w := by
  simpa only [Admin.val?_toAdmin, Option.some.injEq] using congrArg Admin.val? eq

private theorem table_head {f : Frame} {stack : List Val} {dst : Config H}
    (move : FamStep P ⟨s, f, vals stack ++ [.plain (.tableGet tableIndex)]⟩ dst) :
    ∃ (width : AddrType) (i : BitVec width.intType.width) (addr : Nat) (table : TableInst),
      stack = [.num ⟨.int width.intType, i⟩] ∧ s.table? f tableIndex = some (addr, table) ∧
      dst = ⟨s, f, [(table.refs[i.toNat]?.map Admin.ref).getD .trap]⟩ := by
  generalize eq : (⟨s, f, vals stack ++ [.plain (.tableGet tableIndex)]⟩ : Config H) = src at move
  cases move with
  | table step =>
    cases step with
    | getVal lookup entry =>
      obtain ⟨rfl, rfl, code⟩ := Config.mk.inj eq
      obtain ⟨_, rfl, operand, instr⟩ := one_operand code
      obtain rfl := Instr.tableGet.inj (Admin.plain.inj instr)
      exact ⟨_, _, _, _, congrArg List.singleton (of_value_code operand), lookup, by simp [entry]⟩
    | getOob lookup outside =>
      obtain ⟨rfl, rfl, code⟩ := Config.mk.inj eq
      obtain ⟨_, rfl, operand, instr⟩ := one_operand code
      obtain rfl := Instr.tableGet.inj (Admin.plain.inj instr)
      exact ⟨_, _, _, _, congrArg List.singleton (of_value_code operand), lookup,
        by simp [List.getElem?_eq_none_iff.mpr outside]⟩
    | _ =>
      have last := congrArg (fun c : Config H => c.code.getLast?) eq
      simp at last
  | _ =>
    rename_i step
    cases step <;>
      have last := congrArg (fun c : Config H => c.code.getLast?) eq <;> simp at last

private theorem cast_head {f : Frame} {stack : List Val} {rt : RefType} {dst : Config H}
    (move : FamStep P ⟨s, f, vals stack ++ [.plain (.refCast rt)]⟩ dst) :
    ∃ r, stack = [.ref r] ∧
      ((RefOk s r (f.module.instRef rt) ∧ dst = ⟨s, f, [.ref r]⟩) ∨
       (¬ RefOk s r (f.module.instRef rt) ∧ dst = ⟨s, f, [.trap]⟩)) := by
  generalize eq : (⟨s, f, vals stack ++ [.plain (.refCast rt)]⟩ : Config H) = src at move
  cases move with
  | reference step =>
    cases step with
    | castSucceed ok =>
      obtain ⟨rfl, rfl, code⟩ := Config.mk.inj eq
      obtain ⟨_, rfl, operand, instr⟩ := one_operand code
      obtain rfl := Instr.refCast.inj (Admin.plain.inj instr)
      exact ⟨_, congrArg List.singleton (of_value_code operand), .inl ⟨ok, rfl⟩⟩
    | castFail fail =>
      obtain ⟨rfl, rfl, code⟩ := Config.mk.inj eq
      obtain ⟨_, rfl, operand, instr⟩ := one_operand code
      obtain rfl := Instr.refCast.inj (Admin.plain.inj instr)
      exact ⟨_, congrArg List.singleton (of_value_code operand), .inr ⟨fail, rfl⟩⟩
    | _ =>
      have last := congrArg (fun c : Config H => c.code.getLast?) eq
      simp at last
  | _ =>
    rename_i step
    cases step <;>
      have last := congrArg (fun c : Config H => c.code.getLast?) eq <;> simp at last

private theorem family_in_context {f : Frame} {stack : List Val} {head : Instr}
    {rest : List Admin} {dst : Config H}
    (nonvalue : (Admin.plain head).val? = none) (noncontrol : famOf (.plain head) ≠ .control)
    (nonthrow : head ≠ .throwRef)
    (move : Step P noHost ⟨s, f, vals stack ++ .plain head :: rest⟩ dst) :
    ∃ saved used mid, stack = saved ++ used ∧ FamStep P ⟨s, f, vals used ++ [.plain head]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, vals saved ++ mid.code ++ rest⟩ := by
  rcases dst with ⟨_, _, _⟩
  rcases Sim.Step.split_head nonvalue move with ⟨outside, _, _, split, inner, rfl⟩ | ⟨bad, _⟩ | ⟨bad, _⟩
  · obtain ⟨saved, used, mid, shape, family, eq⟩ := inner.noncontrol_vals_inv noncontrol
    obtain ⟨rfl, rfl, rfl⟩ := Config.mk.inj eq
    exact ⟨outside ++ saved, used, mid, by rw [split, shape, List.append_assoc], family,
      by simp only [vals_append, List.append_assoc]⟩
  · cases bad
  · exact (nonthrow (Admin.plain.inj bad)).elim

private theorem table_step_iff {f : Frame} {stack : List Val} {selector : BitVec 32}
    {addr : Nat} {table : TableInst} {rest : List Admin} {dst : Config H}
    (lookup : s.table? f tableIndex = some (addr, table)) :
    Step P noHost ⟨s, f, vals stack ++ constI32 selector :: .plain (.tableGet tableIndex) :: rest⟩ dst ↔
      dst = ⟨s, f, vals stack ++ (table.refs[selector.toNat]?.map Admin.ref).getD .trap :: rest⟩ := by
  constructor
  · intro move
    have shaped : Step P noHost ⟨s, f, vals (stack ++ [.i32 selector]) ++ .plain (.tableGet tableIndex) :: rest⟩ dst := by
      rw [vals_append, List.append_assoc]
      exact move
    obtain ⟨saved, used, mid, split, head, rfl⟩ := family_in_context rfl
      (by simp [famOf]) (by intro impossible; cases impossible) shaped
    obtain ⟨width, i, addr', table', rfl, found, rfl⟩ := table_head head
    obtain ⟨rfl, input⟩ := List.append_inj' split rfl
    rw [lookup] at found
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    cases width with
    | i32 =>
      cases input
      simp only [List.append_assoc, List.singleton_append]
      rfl
    | i64 => cases input
  · rintro rfl
    cases entry : table.refs[selector.toNat]? with
    | none =>
      have step := Step.table (host := noHost) (TableStep.getOob (P := P) (a := .i32) (i := selector) lookup
        (List.getElem?_eq_none_iff.mp entry))
      simpa only [entry, Option.map_none, Option.getD_none, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
        aconst, constI32, Val.toAdmin, Val.i32, AddrType.intType] using
        Sim.Step.vals_left (Sim.Step.append_right (host := noHost) step rest) stack
    | some r =>
      have step := Step.table (host := noHost) (TableStep.getVal (P := P) (a := .i32) (i := selector) lookup entry)
      simpa only [entry, Option.map_some, Option.getD_some, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
        aconst, constI32, Val.toAdmin, Val.i32, AddrType.intType] using
        Sim.Step.vals_left (Sim.Step.append_right (host := noHost) step rest) stack

private theorem cast_step_iff {f : Frame} {stack : List Val} {r : Ref} {rt : RefType}
    {rest : List Admin} {dst : Config H} {ok : Bool}
    (check : RefOk s r (f.module.instRef rt) ↔ ok = true) :
    Step P noHost ⟨s, f, vals stack ++ .ref r :: .plain (.refCast rt) :: rest⟩ dst ↔
      dst = ⟨s, f, vals stack ++ (if ok then .ref r else .trap) :: rest⟩ := by
  constructor
  · intro move
    have shaped : Step P noHost ⟨s, f, vals (stack ++ [.ref r]) ++ .plain (.refCast rt) :: rest⟩ dst := by
      rw [vals_append, List.append_assoc]
      exact move
    obtain ⟨saved, used, mid, split, head, rfl⟩ := family_in_context rfl
      (by simp [famOf]) (by intro impossible; cases impossible) shaped
    obtain ⟨ref, rfl, result⟩ := cast_head head
    obtain ⟨rfl, input⟩ := List.append_inj' split rfl
    cases input
    rcases result with ⟨yes, rfl⟩ | ⟨no, rfl⟩
    · simp [check.mp yes]
    · have falseOk : ok = false := Bool.eq_false_iff.mpr (fun h => no (check.mpr h))
      simp [falseOk]
  · rintro rfl
    cases ok
    · have rejected : ¬ RefOk s r (f.module.instRef rt) := fun yes => by cases check.mp yes
      have step := Step.reference (P := P) (host := noHost) (RefStep.castFail (f := f) rejected)
      exact Sim.Step.vals_left (Sim.Step.append_right step rest) stack
    · have step := Step.reference (P := P) (host := noHost) (RefStep.castSucceed (f := f) (check.mpr rfl))
      exact Sim.Step.vals_left (Sim.Step.append_right step rest) stack

private theorem source_step_iff {caller : Execution.Runtime.Frame} {site : Site} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} {dst : Config H} :
    Step P noHost (coreConfig s caller site selector stack rest .start) dst ↔
      dst = coreConfig s caller site selector stack rest .lookup := by
  have before : coreConfig s caller site selector stack rest .start =
      ⟨s, caller.toCore, vals (stack.map Value.toCore ++ [.i32 selector]) ++
        .plain (.callIndirect tableIndex site.typeIndex) :: rest⟩ := by
    simp [coreConfig, Site.coreCode, constI32, List.append_assoc]
  have after : coreConfig s caller site selector stack rest .lookup =
      ⟨s, caller.toCore, vals (stack.map Value.toCore ++ [.i32 selector]) ++
        .plain (.tableGet tableIndex) :: site.coreCast :: site.coreCall :: rest⟩ := by
    simp [coreConfig, Site.coreCode, constI32, List.append_assoc]
  rw [before, after]
  constructor
  · intro step
    exact step.callIndirect_vals_inv_seq
  · rintro rfl
    exact Sim.Step.vals_left (Sim.Step.append_right (host := noHost) (Step.callIndirect (P := P)
      (s := s) (f := caller.toCore) (x := tableIndex) (y := site.typeIndex)) rest)
      (stack.map Value.toCore ++ [.i32 selector])

private theorem null_step_iff {caller : Execution.Runtime.Frame} {site : Site} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} {dst : Config H} :
    Step P noHost (coreConfig s caller site selector stack rest (.call none)) dst ↔
      dst = coreConfig s caller site selector stack rest .nullTrap := by
  have before : coreConfig s caller site selector stack rest (.call none) =
      ⟨s, caller.toCore, vals (stack.map Value.toCore ++ [.ref .null]) ++ site.coreCall :: rest⟩ := by
    simp [coreConfig, Site.coreCode, coreRef, Val.toAdmin, List.append_assoc]
  rw [before]
  constructor
  · intro move
    rcases move.callRef_top_inv_seq (r := site.coreCall) (by trivial) with
      ⟨saved, split, rfl⟩ | ⟨saved, addr, _, split, _⟩
    · obtain ⟨rfl, _⟩ := List.append_inj' split rfl
      simp [coreConfig, Site.coreCode]
    · cases (List.append_inj' split rfl).2
  · rintro rfl
    simpa [coreConfig, Site.coreCode, Val.toAdmin, List.append_assoc] using
      Sim.Step.vals_left (Sim.Step.append_right (host := noHost)
        (Step.callRefNull (P := P) (s := s) (f := caller.toCore) (c := site.coreCall) trivial) rest)
        (stack.map Value.toCore)

private theorem numeric_types_ok {ctx : TypeCtx} (types : List NumType) :
    TyOk ctx (Ty.ofList (types.map Ty.num)) := by
  induction types with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (.num _) ih

private theorem numeric_ref_ok (nullable : Bool) (sig : V1.FuncType) :
    TyOk ({} : TypeCtx) (Ty.ref nullable (.defHeap sig.toDefType)) := by
  apply TyOk.ref
  apply TyOk.use
  apply TyOk.dt
  unfold V1.FuncType.toDefType
  simp only [liftRec, V1.FuncType.toCoreRec, List.map_cons, List.map_nil, liftSub, liftComp,
    V1.FuncType.toCore, V1.liftResult_toCore]
  exact .defn (.cons (.noSuper (.func (numeric_types_ok _) (numeric_types_ok _))) .nil) (by simp [Ty.length])

private theorem inst_cast {caller : Execution.Runtime.Frame} {site : Site}
    (typeFound : caller.module.types[site.typeIndex.toNat]? = some site.signature) :
    caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩ = .ref true (.defHeap site.signature.toDefType) := by
  simp [ModuleInst.instRef, Execution.Runtime.Frame.toCore, Execution.Runtime.ModuleInst.toCore, liftRef,
    liftHeap, liftTypeIdx, Ty.substAll, Ty.subst, Subst.all, List.getElem?_map, typeFound, Ty.defHeap]

private theorem numeric_cast_iff {caller : Execution.Runtime.Frame} {site : Site} {addr : Execution.Runtime.FuncAddr} {fn : Function}
    (typeFound : caller.module.types[site.typeIndex.toNat]? = some site.signature)
    (allocated : s.funcs[addr.value]? = some fn.coreInstance) :
    RefOk s (.func addr.value) (caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩) ↔
      fn.declaration.type = site.signature := by
  rw [inst_cast typeFound]
  constructor
  · intro ok
    obtain ⟨rt, principal, sub, _⟩ :=
      (RefOk.iff_principal _ _ _ (numeric_ref_ok true site.signature)).mp ok
    simp only [Ref.type?, allocated, Option.map_some, Option.some.injEq] at principal
    subst rt
    have computed := Sub.check_complete TypeCtx.ok_empty rfl sub
      (numeric_ref_ok false fn.declaration.type) (numeric_ref_ok true site.signature)
    simp [Sub.check, Sub.checkK, TypeCtx.checkRef, TypeCtx.checkHeap, TypeCtx.resolve, Ty.defHeap,
      Function.coreInstance] at computed
    exact (V1.FuncType.toDefType_sub_iff _ _ _).mp (TypeCtx.checkDef_sound computed)
  · intro same
    apply RefOk.sub (.func allocated) (numeric_ref_ok true site.signature)
    exact .refNull (.defDef ((V1.FuncType.toDefType_sub_iff _ _ _).mpr same))

theorem trace_exact {caller : Execution.Runtime.Frame} {site : Site} {program : Program} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} {out : Outcome} {addr : Nat}
    (checked : site.check program caller = true) (allocated : program.CoreAllocated s)
    (tableFound : s.table? caller.toCore tableIndex = some (addr, site.table.toCore))
    (resolved : site.resolve program selector = some out) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Step P noHost (coreConfig s caller site selector stack rest a) dst ↔
        dst = coreConfig s caller site selector stack rest b) := by
  have typeFound : caller.module.types[site.typeIndex.toNat]? = some site.signature :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1
  have start (dst : Config H) := source_step_iff (P := P) (s := s) (caller := caller)
    (site := site) (selector := selector) (stack := stack) (rest := rest) (dst := dst)
  have lookup (dst : Config H) := table_step_iff (P := P) (stack := stack.map Value.toCore) (selector := selector)
    (rest := site.coreCast :: site.coreCall :: rest) (dst := dst) tableFound
  have read_entry {entry : Option Execution.Runtime.FuncAddr} (found : site.table.refs[selector.toNat]? = some entry)
      (dst : Config H) :
      Step P noHost (coreConfig s caller site selector stack rest .lookup) dst ↔
      dst = coreConfig s caller site selector stack rest (.cast entry) := by
    cases entry <;> simpa [coreConfig, Site.coreCode, coreRef, Execution.Runtime.TableInst.toCore, found] using lookup dst
  have cast {entry : Option Execution.Runtime.FuncAddr} {ok : Bool} (dst : Config H)
      (check : RefOk s (coreRef entry) (caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩) ↔ ok = true) :=
    cast_step_iff (P := P) (stack := stack.map Value.toCore) (rest := site.coreCall :: rest) (dst := dst) check
  apply List.isChain_cons_cons.mpr
  refine ⟨start, ?_⟩
  cases resolve_iff.mp resolved with
  | bounds entry =>
    refine List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩
    intro dst
    simpa [coreConfig, Site.coreCode, Execution.Runtime.TableInst.toCore, entry] using lookup dst
  | null entry =>
    have pass : RefOk s (coreRef none) (caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩) := by
      rw [inst_cast typeFound]
      exact .sub .null (numeric_ref_ok true site.signature) (.refNull .bot)
    refine List.isChain_cons_cons.mpr ⟨read_entry entry, ?_⟩
    refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨fun _ => null_step_iff, .singleton _⟩⟩
    intro dst
    simpa [coreConfig, Site.coreCode, Site.coreCast] using
      cast (entry := none) dst (show _ ↔ true = true from ⟨fun _ => rfl, fun _ => pass⟩)
  | @mismatch address fn entry found different =>
    have fail : ¬ RefOk s (coreRef (some address)) (caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩) :=
      mt (numeric_cast_iff typeFound (allocated _ _ found)).mp different
    refine List.isChain_cons_cons.mpr ⟨read_entry entry, List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩⟩
    intro dst
    simpa [coreConfig, Site.coreCode, Site.coreCast] using
      cast (entry := some address) dst (show _ ↔ false = true from ⟨fun ok => (fail ok).elim, fun bad => by cases bad⟩)
  | @resolved address fn entry found same =>
    have pass : RefOk s (coreRef (some address)) (caller.toCore.module.instRef ⟨true, .typeIdx site.typeIndex⟩) :=
      (numeric_cast_iff typeFound (allocated _ _ found)).mpr same
    refine List.isChain_cons_cons.mpr ⟨read_entry entry, List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩⟩
    intro dst
    simpa [coreConfig, Site.coreCode, Site.coreCast] using
      cast (entry := some address) dst (show _ ↔ true = true from ⟨fun _ => rfl, fun _ => pass⟩)

theorem trace_reachable {caller : Execution.Runtime.Frame} {site : Site} {selector : BitVec 32}
    {stack : List Value} {rest : List Admin} {out : Outcome}
    (exactSteps : out.coreTrace.IsChain (fun a b => ∀ dst,
      Step P noHost (coreConfig s caller site selector stack rest a) dst ↔
        dst = coreConfig s caller site selector stack rest b))
    {phase : Phase} (member : phase ∈ out.coreTrace) :
    Steps P noHost (coreConfig s caller site selector stack rest .start)
      (coreConfig s caller site selector stack rest phase) := by
  let render := coreConfig s caller site selector stack rest
  have follow (first : Phase) (tail : List Phase)
      (chain : (first :: tail).IsChain (fun a b => ∀ dst, Step P noHost (render a) dst ↔ dst = render b))
      (mem : phase ∈ first :: tail) : Steps P noHost (render first) (render phase) := by
    induction tail generalizing first with
    | nil =>
      obtain rfl : phase = first := List.mem_singleton.mp mem
      exact .refl
    | cons next tail ih =>
      rcases List.mem_cons.mp mem with rfl | later
      · exact .refl
      · obtain ⟨step, more⟩ := List.isChain_cons_cons.mp chain
        exact .head ((step _).mpr rfl) (ih next more later)
  exact follow .start _ exactSteps member

theorem enter_iff {caller : Execution.Runtime.Frame} {site : Site} {program : Program}
    {selector : BitVec 32} {addr : Execution.Runtime.FuncAddr} {fn : Function}
    {saved args : List Value} {rest : List Admin} {dst : Config H}
    (allocated : program.CoreAllocated s) (found : program.lookup addr = some fn)
    (resolved : site.resolve program selector = some (.resolved addr))
    (typed : args.map Value.type = site.signature.params) :
    Step P noHost (coreConfig s caller site selector (saved ++ args) rest (.call (some addr))) dst ↔
      dst = coreEntered s caller fn saved args rest := by
  have same := resolved_signature resolved found
  have params : args.map Value.type = fn.declaration.type.params := by rwa [same]
  have enter := CallContinuation.OuterCall.Computed.Sequence.wasm_call_ref_entry_context_iff
    (P := P) (caller := caller) (saved := saved) (rest := rest) (dst := dst)
    (call := site.coreCall) trivial (allocated _ _ found) params
  have frame := CallContinuation.OuterCall.Computed.Sequence.core_frame_forCall
    fn.declaration.module args fn.declaration.locals
  change Frame.forCall fn.declaration.module.toCore (args.map Value.toCore) fn.coreFunc.locals =
    (fn.declaration.frame args).toCore at frame
  rw [frame] at enter
  simpa only [coreConfig, Site.coreCode, coreRef, coreEntered, CallContinuation.OuterCall.coreValues,
    Option.map_some, Option.getD_some, List.append_assoc, List.cons_append, List.nil_append] using enter

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Proofs.Core
