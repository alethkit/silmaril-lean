module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs

open Execution.Runtime (Frame FuncAddr MemAddr ModuleInst Value)
open Wasm.V1.Execution

theorem append_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {l r : List Admin} :
    CodeAllowed p m rank mod (l ++ r) ↔ CodeAllowed p m rank mod l ∧ CodeAllowed p m rank mod r := by
  simp only [CodeAllowed, List.mem_append, or_imp, forall_and]

theorem single_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {x : Admin} :
    CodeAllowed p m rank mod [x] ↔ Allowed p m rank mod x := by
  simp [CodeAllowed]

theorem value_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (v : Value) :
    Allowed p m rank mod (value v) := by
  rcases v with ⟨t, bits⟩
  cases t with
  | int width => exact .source (.intConst width bits)
  | float width => exact .source (.floatConst width bits)

theorem values_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} (vs : List Value) :
    CodeAllowed p m rank mod (values vs) := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  exact value_allowed v

theorem source_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst} {i : Wasm.V1.Instr}
    (guard : Allowed p m rank mod (.source i)) : SourceAllowed p m rank mod i := by
  cases guard with | source h => exact h

theorem body_allowed {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {a : FuncAddr} {fn : Function} (found : p.lookup a = some fn) :
    CodeAllowed p m fn.rank fn.declaration.module (expression fn.v1Func.body) := by
  obtain ⟨_, supported, _, slot⟩ := p.function_checked checked found
  rw [fn.body_expression, append_allowed]
  refine ⟨values_allowed _, ?_⟩
  intro x member
  obtain ⟨op, used, rfl⟩ := List.mem_map.mp member
  have supportedOp := List.all_eq_true.mp supported op used
  cases op with
  | load offset => exact .source (.load offset slot)
  | store offset => exact .source (.store offset slot)
  | ranked op =>
    cases op with
    | numeric op =>
      cases op with
      | get i => exact .source (.get i)
      | bin t bin => exact .source (.bin t _)
    | set idx => exact .source (.set idx)
    | tee idx => exact .source (.tee idx)
    | unreachable => exact .source .unreachable
    | return_ => exact .source .return_
    | call target =>
      have uses : target ∈ fn.targets :=
        List.mem_flatMap.mpr ⟨.ranked (.call target), used, by simp [Op.targets, Graph.Op.targets]⟩
      obtain ⟨callee, h, resolved, _, smaller⟩ := p.linked_target checked found uses
      exact .source (.call resolved h smaller)
    | _ => contradiction

private theorem label_body {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {n : Nat} {cont : Wasm.V1.Expr} {body : List Admin}
    (h : Allowed p m rank mod (.label n cont body)) : CodeAllowed p m rank mod body := by
  cases h with | label _ guarded => exact guarded

theorem pure_allowed {p : Program} {m : MemAddr} {rank : Nat} {mod : ModuleInst}
    {before after : List Admin} (move : PureStep before after)
    (guard : CodeAllowed p m rank mod before) : CodeAllowed p m rank mod after := by
  cases move with
  | block =>
    have h := source_allowed (guard _ (List.Mem.head _))
    cases h
  | loop =>
    have h := source_allowed (guard _ (List.Mem.head _))
    cases h
  | ifZero | ifNonzero =>
    have h := source_allowed (guard _ (List.Mem.tail _ (List.Mem.head _)))
    cases h
  | brIfNonzero =>
    have h := source_allowed (guard _ (List.Mem.tail _ (List.Mem.head _)))
    cases h
  | brTable =>
    have h := source_allowed (guard _ (List.Mem.tail _ (List.Mem.head _)))
    cases h
  | labelBranch n cont extra vs tail arity =>
    have body := label_body (guard _ (List.Mem.head _))
    have h := source_allowed (body (.source (.br ⟨0⟩)) (by simp))
    cases h
  | labelBranchOuter n cont vs tail idx outer =>
    have body := label_body (guard _ (List.Mem.head _))
    have h := source_allowed (body (.source (.br idx)) (by simp))
    cases h
  | labelReturn n cont vs tail =>
    apply append_allowed.mpr
    exact ⟨values_allowed _, single_allowed.mpr (.source .return_)⟩
  | localTee i v =>
    change CodeAllowed p m rank mod (values [v, v] ++ [.source (.localSet i)])
    exact append_allowed.mpr ⟨values_allowed _, single_allowed.mpr (.source (.set i))⟩
  | _ =>
    first
    | exact values_allowed _
    | exact values_allowed []
    | exact single_allowed.mpr (value_allowed _)
    | exact single_allowed.mpr .trap

theorem edge_module {p : Program} {m : MemAddr} {src dst : State} (move : Edge p m src dst) :
    dst.frame.module = src.frame.module := by
  induction move <;> first | rfl | assumption

theorem edge_extent {p : Program} {m : MemAddr} {src dst : State} (move : Edge p m src dst) :
    dst.bytes.size = src.bytes.size := by
  induction move <;> first | rfl | assumption | exact MemoryWrite.closed_at ‹_›

theorem preserve {p : Program} {m : MemAddr} (checked : p.checkV1 m = true)
    {src dst : State} (move : Edge p m src dst) {rank : Nat}
    (ready : CodeAllowed p m rank src.frame.module src.code) :
    CodeAllowed p m rank dst.frame.module dst.code := by
  induction move generalizing rank with
  | pure move => exact pure_allowed move ready
  | @context bytes bytes' f f' before after move saved tail ih =>
    obtain ⟨leading, suffix⟩ := (append_allowed (l := values saved ++ before) (r := tail)).mp ready
    have middle := ((append_allowed (l := values saved) (r := before)).mp leading).2
    have next := ih middle
    rw [← edge_module move] at suffix
    exact append_allowed.mpr ⟨append_allowed.mpr ⟨values_allowed saved, next⟩, suffix⟩
  | label move n ih =>
    have guard := single_allowed.mp ready
    cases guard with
    | label scalar inside => exact single_allowed.mpr (.label scalar (ih inside))
  | frame move n outer ih =>
    have guard := single_allowed.mp ready
    cases guard with
    | frame found smaller scope arity inside =>
      exact single_allowed.mpr (.frame found smaller ((edge_module move).trans scope) arity (ih inside))
  | get _ => exact single_allowed.mpr (value_allowed _)
  | set _ => exact values_allowed []
  | resolve resolved =>
    have guard := source_allowed (single_allowed.mp ready)
    cases guard with
    | call linked found smaller =>
      cases Option.some.inj (linked.symm.trans resolved)
      exact single_allowed.mpr (.invoke found smaller)
  | @enter bytes f a fn args found count =>
    have guard := single_allowed.mp (append_allowed.mp ready).2
    cases guard with
    | invoke matchesTarget smaller =>
      cases Option.some.inj (found.symm.trans matchesTarget)
      exact single_allowed.mpr (.frame found smaller rfl rfl (single_allowed.mpr
        (.label (p.function_checked checked found).1 (body_allowed checked found))))
  | load slot rule =>
    cases MemoryQuery.invert_at rule with
    | load => exact single_allowed.mpr (.source (.intConst ..))
    | loadTrap => exact single_allowed.mpr .trap
  | store _ _ => exact values_allowed []
  | storeTrap _ _ => exact single_allowed.mpr .trap

theorem initial_call {p : Program} {m : MemAddr} {addr : FuncAddr} {fn : Function}
    {caller : Frame} {index : FuncIdx} (found : p.lookup addr = some fn)
    (resolved : caller.module.funcs[index.toNat]? = some addr) (args : List Value) (bytes : ByteArray) :
    Ready p m (fn.rank + 1) bytes.size ⟨bytes, caller, values args ++ [.source (.call index)]⟩ :=
  ⟨rfl, append_allowed.mpr ⟨values_allowed args,
    single_allowed.mpr (.source (.call resolved found (Nat.lt_succ_self _)))⟩⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.RunProofs
