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

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L : List (Ty κ)}
  (M : Shape.Model.{u,v,w,x} Φ Γ)

theorem env_typed : EnvTyped M.atomType Γ (envOfBound M.raw.bound) := by
  intro i A atSlot
  have hi := List.getElem?_eq_some_iff.mp atSlot
  let j : Fin Γ.length := ⟨i, hi.choose⟩
  rw [envOfBound_agrees M.raw.bound j, ← hi.choose_spec]
  exact M.boundTyped j

theorem term_eval_typed {a : Tm Φ} {A : Ty κ} {s t : M.raw.σ} {b : Value M.raw.α}
    (ha : a.HasType Γ A) (run : Semantics.Tm.Eval M.raw.instr (envOfBound M.raw.bound) a s b t) :
    ValueTyped M.atomType b A :=
  doneTerm_typed (Run.typed M.instrTyped (term_eval_run run .halt) (startTerm_typed (env_typed M) ha))

theorem region_eval_typed {r : LambdaSSA.Region Φ} {s t : M.raw.σ} {i : Nat} {a : Value M.raw.α}
    (hr : r.HasType Γ L) (run : Semantics.Region.Eval M.raw.instr (envOfBound M.raw.bound) r s i a t) :
    ∃ A, At L i A ∧ ValueTyped M.atomType a A :=
  doneRegion_typed (Run.typed M.instrTyped (region_eval_run run .halt) (startRegion_typed (env_typed M) hr))

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape
