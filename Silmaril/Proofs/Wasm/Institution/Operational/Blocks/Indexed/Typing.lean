module

public import Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs

open Execution.Runtime (Value)

private theorem check_values (types stack : List NumType) (args : List Value) (code : List Locals.Op) :
    Locals.check types stack (Locals.values args ++ code) =
      Locals.check types ((args.map Value.type).reverse ++ stack) code := by
  induction args generalizing stack with
  | nil => rfl
  | cons v args ih =>
    rw [show Locals.values (v :: args) ++ code = .value v :: (Locals.values args ++ code) from rfl,
      Locals.check, ih]
    simp [List.reverse_cons, List.append_assoc]

theorem check_source_iff {site : Site} {locals args : List Value} {body : Body} :
    site.checkSource locals args body = true ↔ Admitted site (.source locals args body) := by
  simp only [Site.checkSource, Bool.and_eq_true_iff, decide_eq_true_eq, Admitted, State.Typed, and_assoc]

theorem closed {site : Site} {a b : State} (ready : Admitted site a) (edge : Edge site a b) :
    Admitted site b := by
  refine ⟨ready.1, ?_⟩
  have typed := ready.2
  cases edge with
  | enter locals args body =>
    obtain ⟨localsTyped, argsTyped, ok⟩ := typed
    cases body with
    | locals code =>
      refine ⟨localsTyped, ?_⟩
      simpa [check_values, argsTyped] using (of_decide_eq_true ok :
        Locals.check site.localTypes site.signature.params.reverse code = some site.signature.results.reverse)
    | branch =>
      exact ⟨localsTyped, by simpa [SuffixTyped, argsTyped] using (of_decide_eq_true ok :
        site.signature.params.reverse.take site.signature.results.length = site.signature.results.reverse)⟩
    | return_ =>
      exact ⟨localsTyped, by simpa [SuffixTyped, argsTyped] using (of_decide_eq_true ok :
        site.signature.params.reverse.take site.declaration.results.length = site.declaration.results.reverse)⟩
  | reduce step => exact Locals.closed typed step
  | fallthrough locals results =>
    obtain ⟨localsTyped, stackTyped⟩ := typed
    refine ⟨localsTyped, List.reverse_inj.mp ?_⟩
    change Locals.check site.localTypes [] (Locals.values results) = _ at stackTyped
    rw [← List.append_nil (Locals.values results), check_values, List.append_nil, Locals.check] at stackTyped
    exact Option.some.inj stackTyped
  | branch locals scratch results arity =>
    obtain ⟨localsTyped, stackTyped⟩ := typed
    refine ⟨localsTyped, List.reverse_inj.mp ?_⟩
    have length : ((results.map Value.type).reverse).length = site.signature.results.length := by simpa using arity
    simpa only [SuffixTyped, List.map_append, List.reverse_append, ← length, List.take_left] using stackTyped
  | return_ => exact typed

end Silmaril.Wasm.Institution.Operational.Blocks.Indexed.Proofs
