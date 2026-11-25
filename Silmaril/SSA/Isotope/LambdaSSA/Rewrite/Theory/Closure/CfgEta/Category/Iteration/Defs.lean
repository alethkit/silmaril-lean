module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Feedback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms

/-! # Iteration and case composition in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}
  {A B C : τ} {r s : Region Φ}

/-- Iterate a step to the exact sum type, using the local-label CFG dispatcher. -/
@[expose] def iterateSum
    (f : ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType (Silmaril.coprod B A)) :
    ofType (Φ := Φ) (Γ := Γ) A ⟶ ofType B :=
  InducedCategory.homMk
    (CfgEta.feedback (X := ContinuationContext.single A) (Y := ContinuationContext.single B)
      (f.hom ≫ fromNative.map (SyntacticCategory.iterationDispatchHom A B)))

/-- Iterate a step into the chosen categorical coproduct. -/
@[expose] noncomputable def iterate {X Y : TypeCategory Φ Γ} (f : X ⟶ Y ⨿ X) : X ⟶ Y :=
  let A : τ := X
  let B : τ := Y
  iterateSum (Φ := Φ) (Γ := Γ) (A := A) (B := B)
    (f ≫ (sumIso (Φ := Φ) (Γ := Γ) B A).inv)

theorem singletonValueFamily (hr : ValueBranches (A :: Γ) r [B]) :
    LSubst.ValueFamily Γ [A] [B] (fun _ => r) :=
  fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hr

theorem seqValueBranches (hr : ValueBranches (A :: Γ) r [B])
    (hs : ValueBranches (B :: Γ) s [C]) :
    ValueBranches (A :: Γ) (r.lsubst (fun _ => s.renameVars (lift Nat.succ))) [C] :=
  ((singletonValueFamily hr).comp (singletonValueFamily hs)) (ℓ := 0) (A := A) rfl

/-- The case representative of the copair weakens both arms past the sum payload. -/
theorem caseValueBranches (hr : ValueBranches (A :: Γ) r [C]) (hs : ValueBranches (B :: Γ) s [C]) :
    ValueBranches (Silmaril.coprod A B :: Γ)
      (.case (.var 0) (r.renameVars (lift Nat.succ)) (s.renameVars (lift Nat.succ))) [C] :=
  .case (.var (i := 0) rfl)
    (((singletonValueFamily hr).liftVars (Silmaril.coprod A B)) (ℓ := 0) (A := A) rfl)
    (((singletonValueFamily hs).liftVars (Silmaril.coprod A B)) (ℓ := 0) (A := B) rfl)

end Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
