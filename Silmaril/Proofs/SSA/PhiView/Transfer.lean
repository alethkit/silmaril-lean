module

public import Silmaril.SSA.PhiView.Defs

public section

namespace Silmaril.Proofs.SSA.PhiView

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Terminator Tm VCtx)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.SSA.PhiView

universe u v w x y

variable {Φ : Type u} {τ : Type v} {Source : Type w} {α : Type x} {σ : Type y}
variable [TypeFormers τ] [HasTy Φ τ]
variable {terms : Source → Terminator Φ}
variable {typing : SourceTyping (τ := τ) terms} {params : Nat → List τ}

theorem ofBlockArgs_toBlockArgs (view : View typing params) :
    ofBlockArgs (toBlockArgs view) = view := by
  have same : (ofBlockArgs (toBlockArgs view)).table = view.table := by
    funext label i incoming
    obtain ⟨e, target⟩ := incoming
    cases target
    rfl
  generalize ofBlockArgs (toBlockArgs view) = rebuilt at same ⊢
  cases rebuilt
  cases view
  cases same
  rfl

theorem packTerm_hasType {Γ : VCtx τ} {types : List τ} (args : Arguments Γ types) :
    (packTerm args : Tm Φ).HasType Γ (packedType types) := by
  induction types with
  | nil => exact .unit
  | cons _ _ ih => exact .pair (.var (args 0).property) (ih (fun i => args i.succ))

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem packTerm_eval_iff
    (instr : Φ → Value α → σ → Value α → σ → Prop) {Γ : VCtx τ} {types : List τ}
    (args : Arguments Γ types) (old : Env α) (start finish : σ) (payload : Value α) :
    Isotope.LambdaSSA.Semantics.Tm.Eval instr old (packTerm args) start payload finish ↔
      payload = readArguments args old ∧ finish = start := by
  induction types generalizing finish payload with
  | nil =>
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .unit
  | cons _ _ ih =>
    constructor
    · intro h
      cases h with
      | pair head tail =>
        cases head
        obtain ⟨rfl, rfl⟩ := (ih (fun i => args i.succ) _ _).mp tail
        exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact .pair .var ((ih (fun i => args i.succ) _ _).mpr ⟨rfl, rfl⟩)

theorem latch_eq_transfer
    (instr : Φ → Value α → σ → Value α → σ → Prop)
    (view : View typing params) (edge : EdgeOcc terms) (old : Env α)
    (start finish : σ) (label : Nat) (payload : Value α) :
    Isotope.LambdaSSA.Semantics.Region.Eval instr old
        (.br edge.target edge.argument) start label payload finish ↔
      label = edge.target ∧ payload = latch view edge old ∧ finish = start := by
  rw [← view.packed edge]
  constructor
  · intro h
    cases h with
    | br eval =>
      exact ⟨rfl, (packTerm_eval_iff instr (view.table.column edge) old start finish payload).mp eval⟩
  · rintro ⟨rfl, h⟩
    exact .br ((packTerm_eval_iff instr (view.table.column edge) old start finish payload).mpr h)

end Silmaril.Proofs.SSA.PhiView
