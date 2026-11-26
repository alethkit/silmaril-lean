module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Defs

/-! # Shaped denotation of native continuation representatives -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open LambdaSSA.Region (ContinuationFamily)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {Γ L K : List (Ty κ)}

-- The value and state universes of the model vary independently.
set_option linter.checkUnivs false in
/-- Each continuation is interpreted at its bound payload type and captured context. -/
abbrev Denotation (Φ : Type u) {κ : Type v} [HasTy Φ (Ty κ)] (Γ L K : List (Ty κ)) :=
  (i : Fin L.length) → (M : Shape.Model.{u,v,w,x} Φ (L.get i :: Γ)) → M.raw.σ →
    Behaviour K.length M.raw.α M.raw.σ

def familyMember (f : ContinuationFamily (Φ := Φ) Γ L K) (i : Fin L.length) :
    UB.Typed (Φ := Φ) (L.get i :: Γ) K :=
  ⟨f.val i, (f.property (A := L.get i) (by simp [At])).hasType⟩

/-- Native family denotation uses the existing evaluator, restricted to shaped inputs. -/
noncomputable def familyDenotation (f : ContinuationFamily (Φ := Φ) Γ L K) :
    Denotation.{u,v,w,x} Φ Γ L K :=
  fun i M s => Shape.denote (.native (familyMember f i)) M s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
