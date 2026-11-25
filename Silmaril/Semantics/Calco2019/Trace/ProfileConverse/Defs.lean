module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Thms

/-! # Recovering coproduct feedback from a four-interface operator -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- A trace operator with the domain and codomain guardedness of
Goncharov–Schröder's Definition 25, before imposing the equations. -/
structure FourInterfaceTrace (G : Guardedness P) where
  run {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)} :
    G.TraceGuard f → (P.sum A B ⟶ P.sum C D)
  guarded {A B C D U : K} {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (hf : G.TraceGuard f) : G.guarded (P.inl ≫ run hf)

namespace FourInterfaceTrace

/-- With both external marked ports initial, writing the feedback body in
the four-interface convention adds only coproduct unit maps. -/
def feedbackBody {I A B U : K} (i : IsInitial I) (f : P.sum A U ⟶ P.sum B U) :
    P.sum (P.sum I U) A ⟶ P.sum B (P.sum I U) :=
  restoreTraceBody (tighten f (P.desc (i.to A) (𝟙 A)) P.inl)

def Tightening (T : G.FourInterfaceTrace) : Prop :=
  ∀ {A B C D U A' B' C' D' : K}
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    (a : P.sum A' B' ⟶ P.sum A B) (b : P.sum C D ⟶ P.sum C' D')
    (hf : G.TraceGuard f) (ha : G.guarded (P.inl ≫ a)) (hb : G.guarded (P.inl ≫ b)),
    T.run (traceTighten_guard a b hf ha hb) = a ≫ T.run hf ≫ b

/-- The guarded trace operator induced by a guarded Conway operator. -/
def ofConway (F : G.Conway) : G.FourInterfaceTrace where
  run := F.toFixpoints.guardedTrace
  guarded := F.toFixpoints.guardedTrace_guarded

end FourInterfaceTrace

end Silmaril.Calco2019.Guardedness
