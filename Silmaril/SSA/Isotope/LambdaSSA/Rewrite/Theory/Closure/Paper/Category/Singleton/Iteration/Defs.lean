module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Feedback.Thms

/-! # Singleton iteration in the paper quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open ContinuationContext (single)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {A B : τ}

/-- Dispatch the exact sum of return and state types into outward and local exits. -/
@[expose] def iterateSum (f : ofType (Φ := Φ) A ⟶ ofType (Silmaril.coprod B A)) :
    ofType (Φ := Φ) A ⟶ ofType B :=
  InducedCategory.homMk (feedback (X := single A) (Y := single B)
    (f.hom ≫ fromNative.map (SyntacticCategory.iterationDispatchHom A B)))

/-- Convert the chosen sum and send each summand to its guarded CFG label. -/
@[expose] noncomputable def iterationDispatchArrow (A B : TypeCategory (τ := τ) Φ) :
    (toInterface Φ).obj (B ⨿ A) ⟶
      Paper.fromNative.obj ((single (show τ from A)).append (single (show τ from B))) :=
  (sumIso (Φ := Φ) (show τ from B) (show τ from A)).inv.hom ≫
    Paper.fromNative.map (SyntacticCategory.iterationDispatchHom (show τ from A) (show τ from B))

/-- Feed the state summand of a step back to its input. -/
@[expose] noncomputable def iterate {X Y : TypeCategory (τ := τ) Φ} (f : X ⟶ Y ⨿ X) : X ⟶ Y :=
  iterateSum (A := (show τ from X)) (B := (show τ from Y))
    (f ≫ (sumIso (Φ := Φ) (show τ from Y) (show τ from X)).inv)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
