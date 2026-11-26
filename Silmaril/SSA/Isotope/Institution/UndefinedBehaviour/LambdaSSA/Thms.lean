module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Comparison

/-! # Limits of encoding LambdaSSA region UB with expression primitives -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB

open Institution.Observational

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

theorem refines_iff {Γ : VCtx τ} {L : LCtx τ} (r s : Typed (Φ := Φ) Γ L) :
    Refines.{u,v,w,x} r s ↔
      ∀ M : Model.{u,w,x} Φ Γ.length, observe M r ⊆ observe M s :=
  (lambdaSSA.{u,w,x} Φ L.length).obsLe_iff _ _

/-- At the empty-label boundary, typing requires at least one local block.
A primitive can supply an expression for a let or branch argument only. -/
theorem not_noLocalBlocks (Γ : VCtx τ) (r : Typed (Φ := Φ) Γ []) : ¬ r.val.NoLocalBlocks :=
  fun h => Proofs.Isotope.LambdaSSA.UB.noLocalBlocks_not_scoped h r.property.scoped

/-- In the fault-only instruction model, the faulting prefix and the diverging
backedge have no common upper bound even among arbitrary typed nested CFGs. -/
theorem no_common_upper_bound (Γ : VCtx τ) (L : LCtx τ) (f : Φ)
    (source : instrSrc f = (unit : τ)) :
    ¬ ∃ r : Typed (Φ := Φ) Γ L,
      observe (faultModel.{u,w,x} Φ Γ.length) (primitiveThenLoop Γ L f source) ⊆
        observe (faultModel.{u,w,x} Φ Γ.length) r ∧
      observe (faultModel.{u,w,x} Φ Γ.length) (loop Γ L) ⊆
        observe (faultModel.{u,w,x} Φ Γ.length) r :=
  Proofs.Isotope.LambdaSSA.UB.no_common_upper_bound Γ L f source

/-- No native typed region is greatest for refinement over all models of an
alphabet with a unit-taking primitive. This includes the empty-label judgment. -/
theorem no_greatest (Γ : VCtx τ) (L : LCtx τ) (f : Φ) (source : instrSrc f = (unit : τ)) :
    ¬ ∃ r : Typed (Φ := Φ) Γ L, ∀ a : Typed (Φ := Φ) Γ L, Refines.{u,v,w,x} a r :=
  fun ⟨r, h⟩ => no_common_upper_bound Γ L f source
    ⟨r, (refines_iff _ _).mp (h (primitiveThenLoop Γ L f source)) _,
      (refines_iff _ _).mp (h (loop Γ L)) _⟩

/-- A typed region with no external labels has only fault and divergence observations. -/
theorem observe_subset_empty {Γ : VCtx τ} (M : Model.{u,w,x} Φ Γ.length)
    (r : Typed (Φ := Φ) Γ []) :
    observe M r ⊆ emptyObservations M.α M.σ :=
  Proofs.Isotope.LambdaSSA.UB.observe_subset_empty M r

/-- At a fixed model and with no external labels, the unit-fed prefix attains
greatest behaviour if the primitive can fault to every state and can always
either diverge itself or return to the internal backedge. -/
theorem observe_primitiveThenLoop_eq_empty {Γ : VCtx τ} (M : Model.{u,w,x} Φ Γ.length)
    (f : Φ) (source : instrSrc f = (unit : τ))
    (faults : ∀ s s', M.faults f .unit s s')
    (continues : ∀ s, M.prim f .unit s ∨ ∃ value s', M.instr f .unit s value s') :
    observe M (primitiveThenLoop Γ [] f source) = emptyObservations M.α M.σ :=
  Proofs.Isotope.LambdaSSA.UB.observe_primitiveThenLoop_eq_empty M f source faults continues

end Silmaril.Isotope.LambdaSSA.UB
