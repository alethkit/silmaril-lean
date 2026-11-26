module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Syntactic.Defs

/-! # Overlay semantics of exact native representatives -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay

open Institution.Observational

universe u v w x

-- The value and state universe of the model vary independently.
set_option linter.checkUnivs false in
/-- Dependence on the observational model, captured values, and initial state. -/
abbrev Denotation (Φ : Type u) {τ : Type v} (Γ L : List τ) :=
  (M : Model.{u,w,x} Φ Γ.length) → M.σ → Behaviour L.length M.α M.σ

variable {Φ : Type u} {τ : Type v} [TypeFormers τ] [HasTy Φ τ] {Γ L : List τ}

/-- The representative map uses the native constructor of the UB overlay. -/
noncomputable def nativeDenotation (r : LambdaSSA.Region.TypedRegion (Φ := Φ) Γ L) :
    Denotation.{u,v,w,x} Φ Γ L :=
  denote (.native ⟨r.val, r.property⟩)

end Silmaril.Isotope.LambdaSSA.UB.Overlay
