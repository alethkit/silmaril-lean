module

public import Silmaril.SSA.MLIR.Module.Symbols.Defs
public import Silmaril.SSA.MLIR.Module.Thms

/-! Lookup, admission, and stability of the function signature environment. -/

public section

namespace Silmaril.MLIR

universe u v w w'

variable {I : Type u} {O : Type v} {B : I → O → Type w} {C : I → O → Type w'}

@[simp] theorem FuncModule.signatures_names (mod : FuncModule B) :
    mod.signatures.funcs.map Prod.fst = mod.funcs.map Prod.fst := by
  simp [signatures, Module.map, List.map_map, Function.comp_def]

@[simp] theorem FuncModule.signatures_find? (mod : FuncModule B) (name : String) :
    mod.signatures.find? name = (mod.find? name).map FuncOf.signature :=
  Module.find?_map FuncOf.signature mod name

/-- A body translation at fixed interfaces leaves the whole signature table unchanged. -/
@[simp] theorem FuncModule.signatures_map (mod : FuncModule B)
    (body : ∀ {i o}, B i o → C i o) : (mod.map id id body).signatures = mod.signatures := by
  change Module.map FuncOf.signature (Module.map (FuncOf.map id id body) mod) = _
  rw [Module.map_comp]
  rfl

@[simp] theorem DirectCall.resolve?_isSome [DecidableEq I] [DecidableEq O]
    (symbols : Module (FuncSignature I O)) (callee : String) (inputs : I) (outputs : O) :
    (DirectCall.resolve? symbols callee inputs outputs).isSome ↔
      symbols.find? callee = some ⟨inputs, outputs⟩ := by
  by_cases found : symbols.find? callee = some ⟨inputs, outputs⟩ <;> simp [resolve?, found]

theorem DirectCall.callee_of_resolve? [DecidableEq I] [DecidableEq O]
    {symbols : Module (FuncSignature I O)} {callee : String} {inputs : I} {outputs : O}
    {call : DirectCall symbols inputs outputs}
    (accepted : DirectCall.resolve? symbols callee inputs outputs = some call) :
    call.callee = callee := by
  unfold resolve? at accepted
  split at accepted <;> cases accepted <;> rfl

@[simp] theorem DirectCall.resolve?_callee [DecidableEq I] [DecidableEq O]
    {symbols : Module (FuncSignature I O)} {inputs : I} {outputs : O}
    (call : DirectCall symbols inputs outputs) :
    DirectCall.resolve? symbols call.callee inputs outputs = some call := by
  cases call with
  | mk callee found => simp [resolve?, found]

/-- The result, including its typed evidence, agrees after a body-only translation.
The two result types are indexed by the equal signature tables. -/
theorem FuncModule.resolveDirectCall?_map [DecidableEq I] [DecidableEq O] (mod : FuncModule B)
    (body : ∀ {i o}, B i o → C i o) (callee : String) (inputs : I) (outputs : O) :
    HEq (DirectCall.resolve? (mod.map id id body).signatures callee inputs outputs)
      (DirectCall.resolve? mod.signatures callee inputs outputs) := by
  rw [mod.signatures_map body]

end Silmaril.MLIR
