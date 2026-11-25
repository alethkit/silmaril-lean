module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Interpretation.Thms
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Expansion.Thms
public import Silmaril.Semantics.Calco2019.Trace.Uniformity.Thms

/-! # The commutative schema on chosen finite copowers -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.IterationTheory.FiniteCopowers

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
  (C : FiniteCopowers X)

/-- Take the row selected by the projection, then route its recursive outputs
within the fibers for the corresponding large-system row. -/
def routedBody {S T : Type} [Finite S] [Finite T] (p : S → T) (route : S → S → S)
    (f : (C.cofan T).pt ⟶ P.sum Y (C.cofan S).pt) : (C.cofan S).pt ⟶ P.sum Y (C.cofan S).pt :=
  Cofan.IsColimit.desc (C.colimit S) (fun s =>
    (C.cofan T).inj (p s) ≫ f ≫ P.map (𝟙 Y) (C.reindex (route s)))

/-- The surjective commutative schema for a total iteration operator. -/
def CommutativeIdentities (F : (Guardedness.greatest P).Fixpoints) : Prop :=
  ∀ {S T : Type} [Finite S] [Finite T] {Y : K}
    (p : S → T) (_ : Function.Surjective p) (route : S → S → S)
    (_ : ∀ i j, p (route i j) = p j)
    (f : (C.cofan T).pt ⟶ P.sum Y (C.cofan S).pt),
    F.iterate (C.routedBody p route f) True.intro =
      C.reindex p ≫ F.iterate (f ≫ P.map (𝟙 Y) (C.reindex p)) True.intro

end Silmaril.Calco2019.IterationTheory.FiniteCopowers
