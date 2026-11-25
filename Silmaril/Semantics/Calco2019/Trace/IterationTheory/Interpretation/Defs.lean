module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Observations.Thms
public import Silmaril.Semantics.Calco2019.Trace.Automata.Thms

/-! # Interpreting ranked systems in a co-Cartesian category -/

@[expose] public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}

/-- Chosen finite copowers of one object. A sorted iteration theory takes
this object to be the generator of its natural-number objects. -/
structure FiniteCopowers (X : K) where
  cofan (I : Type) [Finite I] : Cofan (fun _ : I => X)
  colimit (I : Type) [Finite I] : IsColimit (cofan I)

namespace FiniteCopowers

variable {I J : Type} [Finite I] [Finite J]

/-- The base map associated with a function between finite index sets. -/
def reindex (C : FiniteCopowers X) (f : I → J) : (C.cofan I).pt ⟶ (C.cofan J).pt :=
  stateReindex (a := C.cofan J) (C.colimit I) f

/-- Uniformity with respect to finite base maps between these copowers. -/
def BaseUniform (C : FiniteCopowers X) (F : (Guardedness.greatest P).Fixpoints) : Prop :=
  ∀ {I J : Type} [Finite I] [Finite J] (f : I → J), F.UniformAt (C.reindex f)

end FiniteCopowers

/-- Interpret operations and parameter exits at one result object. A common
value for bottom is used when comparing systems at that result object. -/
structure Interpretation (C : FiniteCopowers X) (σ : Signature.{w}) (E : Type z) (Y : K) where
  op (s : σ.Symbol) : X ⟶ (C.cofan (Fin (σ.arity s))).pt
  exit : E → (X ⟶ Y)
  bottom : X ⟶ Y

namespace Interpretation

variable {C : FiniteCopowers X} {σ : Signature.{w}} {E : Type z}
  (M : Interpretation C σ E Y) {S : Type} [Finite S]

/-- Interpret one head, injecting recursive results into the state summand. -/
def branch (e : Head σ E S) : X ⟶ P.sum Y (C.cofan S).pt :=
  match e with
  | .bottom => M.bottom ≫ P.inl
  | .exit p => M.exit p ≫ P.inl
  | .node sym child => M.op sym ≫ C.reindex child ≫ P.inr

/-- Assemble the equations into a categorical iteration body. -/
def body (g : System σ E S) : (C.cofan S).pt ⟶ P.sum Y (C.cofan S).pt :=
  Cofan.IsColimit.desc (C.colimit S) (fun s => M.branch (P := P) (g s))

/-- Read the component at a designated state after iteration. -/
def solution (F : (Guardedness.greatest P).Fixpoints) (g : System σ E S) (s : S) : X ⟶ Y :=
  (C.cofan S).inj s ≫ F.iterate (M.body g) True.intro

end Interpretation

end Silmaril.Calco2019.IterationTheory
