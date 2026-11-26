module

public import Silmaril.SSA.PhiView.Defs
import Silmaril.Proofs.SSA.PhiView.Transfer

/-! # Round trips and selected-edge agreement for the explicit φ view -/

public section

namespace Silmaril.SSA.PhiView

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (At Terminator Tm VCtx)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x y

variable {Φ : Type u} {τ : Type v} {Source : Type w} {α : Type x} {σ : Type y}
variable [TypeFormers τ] [HasTy Φ τ]
variable {terms : Source → Terminator Φ}
variable {typing : SourceTyping (τ := τ) terms} {params : Nat → List τ}

@[simp] theorem toBlockArgs_ofBlockArgs (args : BlockArgs typing params) :
    toBlockArgs (ofBlockArgs args) = args := rfl

@[simp] theorem ofBlockArgs_toBlockArgs (view : View typing params) :
    ofBlockArgs (toBlockArgs view) = view :=
  Proofs.SSA.PhiView.ofBlockArgs_toBlockArgs view

theorem packTerm_hasType {Γ : VCtx τ} {types : List τ} (args : Arguments Γ types) :
    (packTerm args : Tm Φ).HasType Γ (packedType types) :=
  Proofs.SSA.PhiView.packTerm_hasType args

/-- A certified table emits the original branch at each occurrence. -/
theorem branch_eq (view : View typing params) (edge : EdgeOcc terms) :
    view.table.branch edge = .br edge.target edge.argument := by
  rw [Table.branch, view.packed edge]

theorem branch_hasType (table : Table typing params) (edge : EdgeOcc terms)
    {labels : List τ} (target : At labels edge.target (packedType (params edge.target))) :
    (table.branch edge).HasType (typing.scope edge) labels :=
  .br target (packTerm_hasType (table.column edge))

/-- Once an occurrence is selected, the ordinary λSSA branch evaluates to
exactly that target and the simultaneously latched payload, leaving state
unchanged. This is a single transfer law. -/
theorem latch_eq_transfer
    (instr : Φ → Value α → σ → Value α → σ → Prop)
    (view : View typing params) (edge : EdgeOcc terms) (old : Env α)
    (start finish : σ) (label : Nat) (payload : Value α) :
    Isotope.LambdaSSA.Semantics.Region.Eval instr old
        (.br edge.target edge.argument) start label payload finish ↔
      label = edge.target ∧ payload = latch view edge old ∧ finish = start :=
  Proofs.SSA.PhiView.latch_eq_transfer instr view edge old start finish label payload

end Silmaril.SSA.PhiView
