module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape
open Silmaril.Isotope.Morphism.SSAIter (envOfBound envOfBound_agrees)
open Silmaril.Isotope.LambdaSSA.Resumption
open Silmaril.Isotope.LambdaSSA.Resumption.Typing
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}

section
variable {α : Type w} {σ : Type x} {atomType : α → κ → Prop} {env : Env α}
  {instr : Φ → Value α → σ → Value α → σ → Prop}

theorem term_eval_typed_at (steps : InstrTyped atomType instr) (shaped : EnvTyped atomType Γ env)
    {a : Tm Φ} {A : Ty κ} {s t : σ} {b : Value α}
    (ha : a.HasType Γ A) (run : Semantics.Tm.Eval instr env a s b t) : ValueTyped atomType b A :=
  doneTerm_typed (Run.typed steps (term_eval_run run .halt) (startTerm_typed shaped ha))

theorem region_eval_typed_at (steps : InstrTyped atomType instr) (shaped : EnvTyped atomType Γ env)
    {r : LambdaSSA.Region Φ} {s t : σ} {i : Nat} {a : Value α}
    (hr : r.HasType Γ L) (run : Semantics.Region.Eval instr env r s i a t) :
    ∃ A, At L i A ∧ ValueTyped atomType a A :=
  doneRegion_typed (Run.typed steps (region_eval_run run .halt) (startRegion_typed shaped hr))
end

variable (M : Shape.Model.{u,v,w,x} Φ Γ)

theorem env_typed : EnvTyped M.atomType Γ (envOfBound M.raw.bound) := by
  intro i A atSlot
  have hi := List.getElem?_eq_some_iff.mp atSlot
  let j : Fin Γ.length := ⟨i, hi.choose⟩
  rw [envOfBound_agrees M.raw.bound j, ← hi.choose_spec]
  exact M.boundTyped j

theorem term_eval_typed {a : Tm Φ} {A : Ty κ} {s t : M.raw.σ} {b : Value M.raw.α}
    (ha : a.HasType Γ A) (run : Semantics.Tm.Eval M.raw.instr (envOfBound M.raw.bound) a s b t) :
    ValueTyped M.atomType b A :=
  term_eval_typed_at M.instrTyped (env_typed M) ha run

theorem region_eval_typed {r : LambdaSSA.Region Φ} {s t : M.raw.σ} {i : Nat} {a : Value M.raw.α}
    (hr : r.HasType Γ L) (run : Semantics.Region.Eval M.raw.instr (envOfBound M.raw.bound) r s i a t) :
    ∃ A, At L i A ∧ ValueTyped M.atomType a A :=
  region_eval_typed_at M.instrTyped (env_typed M) hr run

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape
