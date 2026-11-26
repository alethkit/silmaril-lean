module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Source.Check

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Proofs

open Execution
open Execution.Runtime (Value)
open CallContinuation.OuterCall
open CallContinuation.OuterCall.Computed
open CallContinuation.OuterCall.Ranked
open Wasm.SingleThreaded.Det (noHost)
open Blocks.Context (Scope)

private theorem improve_chain {A : Type} {R S : A → A → Prop} {xs : List A}
    (chain : xs.IsChain R) (lift : ∀ a ∈ xs.dropLast, ∀ b, R a b → S a b) : xs.IsChain S := by
  induction chain with
  | nil => exact .nil
  | singleton => exact .singleton _
  | cons_cons head tail ih =>
    apply List.isChain_cons_cons.mpr
    refine ⟨lift _ (by simp) _ head, ih ?_⟩
    intro a mem b step
    exact lift a (by simp [mem]) b step

theorem core_nest_step_with {A H : Type} {P : Numerics.Profile} {a : Core.Config H}
    (stays : ∀ n out, ¬ Core.LabelExit n [] a.code out)
    (emit : A → Core.Admin) (scopes : List (Scope A)) :
    (∀ n out, ¬ Core.LabelExit n [] (Context.coreNestWith emit scopes a).code out) ∧
      (∀ dst, Core.Step P noHost (Context.coreNestWith emit scopes a) dst ↔
        ∃ mid, Core.Step P noHost a mid ∧ dst = Context.coreNestWith emit scopes mid) := by
  induction scopes with
  | nil => exact ⟨stays, fun _ => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩⟩
  | cons scope rest ih =>
    constructor
    · intro n out
      simp only [Context.coreNestWith, List.foldr_cons]
      exact core_label_stays (head := .label scope.arity [] _) rfl (by simp) (by simp)
        (by simp [Core.Admin.IsReturnCallRef]) (by simp) (by simp)
    · intro dst
      let before := Context.coreNestWith emit rest a
      have casesStep := Blocks.Context.core_label_iff (P := P) (s := before.store) (f := before.frame)
        (n := scope.arity) (saved := (scope.saved.map Value.toCore)) (body := before.code)
        (rest := scope.rest.map emit) (dst := dst)
      constructor
      · intro move
        rcases casesStep.mp move with ⟨mid, step, eq⟩ | ⟨out, pop, _⟩
        · obtain ⟨next, edge, rfl⟩ := (ih.2 mid).mp step
          exact ⟨next, edge, eq⟩
        · exact (ih.1 _ out pop).elim
      · rintro ⟨mid, edge, rfl⟩
        exact casesStep.mpr (.inl ⟨_, (ih.2 _).mpr ⟨mid, edge, rfl⟩, rfl⟩)

theorem core_nest_step {H : Type} {P : Numerics.Profile} {a : Core.Config H}
    (stays : ∀ n out, ¬ Core.LabelExit n [] a.code out)
    (scopes : List (Scope Graph.Op)) :
    (∀ n out, ¬ Core.LabelExit n [] (coreNest scopes a).code out) ∧
      (∀ dst, Core.Step P noHost (coreNest scopes a) dst ↔
        ∃ mid, Core.Step P noHost a mid ∧ dst = coreNest scopes mid) :=
  core_nest_step_with (P := P) stays Graph.coreEmit scopes

private theorem core_nest {H : Type} {P : Numerics.Profile} {a b : Core.Config H}
    (stays : ∀ n out, ¬ Core.LabelExit n [] a.code out)
    (exactStep : ∀ dst, Core.Step P noHost a dst ↔ dst = b)
    (scopes : List (Scope Graph.Op)) (dst : Core.Config H) :
    Core.Step P noHost (coreNest scopes a) dst ↔ dst = coreNest scopes b := by
  rw [(core_nest_step (P := P) stays scopes).2]
  simp only [exactStep, exists_eq_left]

theorem core_resolution_allocated {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {active : Activation} {program : Graph.Program} {tables : Tables} {out : Outcome}
    (ready : active.Checked program tables) (allocated : active.binding.site.CoreAllocated program s)
    (tableAllocated : Tables.CoreAllocated tables s) (resolved : active.resolve program = some out)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) :
    out.coreTrace.IsChain (fun a b => ∀ dst,
      Core.Step P noHost (active.coreConfig s scopes tail a) dst ↔ dst = active.coreConfig s scopes tail b) := by
  have chain := Indirect.core_trace_allocated_exact (P := P) (stack := active.operands.saved ++ active.operands.args)
    (rest := tail.map Graph.coreEmit) ready.site allocated (core_table ready tableAllocated) resolved
  have pending (a : Indirect.Phase) (mem : a ∈ (out.coreTrace).dropLast) : a.Pending := by
    cases out <;>
      simp only [Outcome.coreTrace, List.cons_append, List.nil_append, List.dropLast_cons_cons,
        List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at mem <;>
      rcases mem with rfl | rfl | rfl | rfl <;> trivial
  exact improve_chain chain fun a mem _ step =>
    core_nest (Indirect.core_lookup_stays (pending a mem)) step scopes

theorem core_entry {H : Type} {P : Numerics.Profile} {s : Core.Store H}
    {active : Activation} {program : Graph.Program} {tables : Tables} {call : Context.Invocation}
    (ready : active.Checked program tables) (allocated : program.CoreAllocated s)
    (invoked : active.invocation program = some call)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Core.Config H) :
    Core.Step P noHost (active.coreConfig s scopes tail (.call (some call.address))) dst ↔
      dst = coreNest scopes (Indirect.coreEntered s call.caller call.callee call.saved call.args
        (tail.map Graph.coreEmit)) := by
  obtain ⟨address, _, resolved, found, rfl⟩ := invocation_fields invoked
  exact core_nest (Indirect.core_lookup_stays (phase := .call (some address)) trivial)
    (fun _ => Indirect.core_enter_iff allocated found resolved ready.args) scopes dst

open Wasm.Lime1.Execution in
theorem lime_nest_step_with {A H : Type} {a : Config H}
    (stays : ∀ n out, ¬ PureStep a.frame.module.types [.label n [] a.code] out)
    (emit : A → Admin) (scopes : List (Scope A)) :
    (∀ n out, ¬ PureStep (Context.limeNestWith emit scopes a).frame.module.types [.label n [] (Context.limeNestWith emit scopes a).code] out) ∧
      (∀ dst, Step CallFrame.limeNoHost (Context.limeNestWith emit scopes a) dst ↔
        ∃ mid, Step CallFrame.limeNoHost a mid ∧ dst = Context.limeNestWith emit scopes mid) := by
  induction scopes with
  | nil => exact ⟨stays, fun _ => ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, rfl⟩ => h⟩⟩
  | cons scope rest ih =>
    constructor
    · intro n out
      simp only [Context.limeNestWith, List.foldr_cons]
      exact lime_label_stays (head := .label scope.arity [] _) rfl (by simp) (by simp)
        (by simp)
    · intro dst
      let before := Context.limeNestWith emit rest a
      have casesStep := Blocks.Context.lime_label_iff (s := before.store) (f := before.frame)
        (n := scope.arity) (saved := scope.saved) (body := before.code)
        (rest := scope.rest.map emit) (dst := dst)
      constructor
      · intro move
        rcases casesStep.mp move with ⟨mid, step, eq⟩ | ⟨out, pop, _⟩
        · obtain ⟨next, edge, rfl⟩ := (ih.2 mid).mp step
          exact ⟨next, edge, eq⟩
        · exact (ih.1 _ out pop).elim
      · rintro ⟨mid, edge, rfl⟩
        exact casesStep.mpr (.inl ⟨_, (ih.2 _).mpr ⟨mid, edge, rfl⟩, rfl⟩)

open Wasm.Lime1.Execution in
theorem lime_nest_step {H : Type} {a : Config H}
    (stays : ∀ n out, ¬ PureStep a.frame.module.types [.label n [] a.code] out)
    (scopes : List (Scope Graph.Op)) :
    (∀ n out, ¬ PureStep (limeNest scopes a).frame.module.types [.label n [] (limeNest scopes a).code] out) ∧
      (∀ dst, Step CallFrame.limeNoHost (limeNest scopes a) dst ↔
        ∃ mid, Step CallFrame.limeNoHost a mid ∧ dst = limeNest scopes mid) :=
  lime_nest_step_with stays Graph.limeEmit scopes

open Wasm.Lime1.Execution in
private theorem lime_nest {H : Type} {a b : Config H}
    (stays : ∀ n out, ¬ PureStep a.frame.module.types [.label n [] a.code] out)
    (exactStep : ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b)
    (scopes : List (Scope Graph.Op)) (dst : Config H) :
    Step CallFrame.limeNoHost (limeNest scopes a) dst ↔ dst = limeNest scopes b := by
  rw [(lime_nest_step stays scopes).2]
  simp only [exactStep, exists_eq_left]

open Wasm.Lime1.Execution in
theorem lime_resolution_allocated {H : Type} {s : Store H} {active : Activation} {program : Graph.Program}
    {tables : Tables} {out : Outcome}
    (ready : active.Checked program tables) (allocated : active.binding.site.LimeAllocated program s)
    (tableAllocated : Tables.LimeAllocated tables s) (resolved : active.resolve program = some out)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Config H) :
    Step CallFrame.limeNoHost (active.limeSource s scopes tail) dst ↔ dst = active.limeResolved s scopes tail out :=
  lime_nest (a := Indirect.limeSource s active.caller active.binding.site active.operands.selector
      (active.operands.saved ++ active.operands.args) (tail.map Graph.limeEmit))
    Indirect.lime_lookup_stays
    (fun _ => Indirect.lime_step_allocated_iff ready.site allocated (lime_table ready tableAllocated) resolved)
    scopes dst

open Wasm.Lime1.Execution in
theorem lime_entry {H : Type} {s : Store H} {active : Activation} {program : Graph.Program}
    {tables : Tables} {call : Context.Invocation}
    (ready : active.Checked program tables) (allocated : program.LimeAllocated s)
    (invoked : active.invocation program = some call)
    (scopes : List (Scope Graph.Op)) (tail : List Graph.Op) (dst : Config H) :
    Step CallFrame.limeNoHost (active.limeResolved s scopes tail (.resolved call.address)) dst ↔
      dst = limeNest scopes (Indirect.limeEntered s call.caller call.callee call.saved call.args
        (tail.map Graph.limeEmit)) := by
  obtain ⟨_, _, resolved, found, rfl⟩ := invocation_fields invoked
  exact lime_nest Indirect.lime_invoke_stays
    (fun _ => Indirect.lime_enter_iff allocated found resolved ready.args) scopes dst

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Source.Proofs
