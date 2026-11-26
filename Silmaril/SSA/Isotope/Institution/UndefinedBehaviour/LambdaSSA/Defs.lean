module

public import Silmaril.SSA.Isotope.Institution.Observational.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Defs

/-! # A unit-fed expression primitive and the LambdaSSA region boundary -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB

open Institution.Observational

universe u v w x

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Native regions at a fixed value context and label interface. -/
abbrev Typed (Γ : VCtx τ) (L : LCtx τ) := {r : Region Φ // r.HasType Γ L}

/-- Observe a typed region in the repository's observational institution. -/
def observe {Γ : VCtx τ} {L : LCtx τ} (M : Model.{u,w,x} Φ Γ.length)
    (r : Typed (Φ := Φ) Γ L) : Set (Observation (Nat × Value M.α) M.σ) :=
  ssaBeh L.length M ⟨r.val, r.property.scoped⟩

/-- More permissive regions are on the right. The order compares inclusion of
returns, faults and divergence uniformly over all observational models. -/
def Refines {Γ : VCtx τ} {L : LCtx τ} (r s : Typed (Φ := Φ) Γ L) : Prop :=
  (lambdaSSA.{u,w,x} Φ L.length).ObsLe ⟨r.val, r.property.scoped⟩ ⟨s.val, s.property.scoped⟩

/-- An internal unit-state backedge gives a typed region with any external interface. -/
def loop (Γ : VCtx τ) (L : LCtx τ) : Typed (Φ := Φ) Γ L :=
  ⟨.cfg (.br 0 .unit) 1 (fun _ => .br 0 (.var 0)),
    .cfg (fun _ : Fin 1 => unit) (.br (ℓ := 0) rfl .unit)
      (fun _ => .br (ℓ := 0) rfl (.var (i := 0) rfl))⟩

/-- Sequence the unit-fed primitive before a local backedge. In particular this
gives a typed region for the empty external interface. -/
def primitiveThenLoop (Γ : VCtx τ) (L : LCtx τ) (f : Φ) (hf : instrSrc f = (unit : τ)) : Typed (Φ := Φ) Γ L :=
  ⟨.let₁ (.op f .unit) (loop (Φ := Φ) ((instrTrg f : τ) :: Γ) L).val,
    .let₁ (.op (hf ▸ .unit)) (loop (Φ := Φ) ((instrTrg f : τ) :: Γ) L).property⟩

/-- A deterministic observation model in which each primitive faults, with no
successful primitive step and no primitive divergence. -/
def faultModel (Φ : Type u) (n : Nat) : Model.{u,w,x} Φ n where
  α := PUnit
  σ := PUnit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := True
  prim _ _ _ := False
  bound _ := .unit

/-- The greatest set of observations that respects an empty label interface.
It includes every fault and every divergence. -/
def emptyObservations (α : Type w) (σ : Type x) : Set (Observation (Nat × Value α) σ) :=
  {o | match o with
    | .ret _ _ _ => False
    | .fault _ _ | .diverge _ => True}

end Silmaril.Isotope.LambdaSSA.UB
