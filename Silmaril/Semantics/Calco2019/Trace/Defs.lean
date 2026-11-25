module

public import Silmaril.Semantics.Calco2019.Thms

/-! # Co-Cartesian guarded feedback in Remark 15

The maps below are the Conway-to-trace and trace-to-Conway formulas of
Goncharov and Schröder, *Guarded Traced Categories*, Proposition 32.
-/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

namespace Guardedness

/-- In feedback form the body is required to be guarded from the recursive
input to the recursive output. -/
def FeedbackGuard (G : Guardedness P) {A B U : K} (f : P.sum A U ⟶ P.sum B U) : Prop :=
  G.guarded (P.inr ≫ f)

/-- The operation type for co-Cartesian feedback. -/
abbrev Feedback (G : Guardedness P) :=
  ∀ {A B U : K} (f : P.sum A U ⟶ P.sum B U), G.FeedbackGuard f → (A ⟶ B)

/-- Feed back the recursive branch using the given fixpoint operator. -/
def Fixpoints.feedback (F : G.Fixpoints) : G.Feedback :=
  fun f hf => P.inl ≫ f ≫ P.desc (𝟙 _) (F.iterate (P.inr ≫ f) hf)

/-- Run the same body on the entry and feedback branches to recover iteration. -/
def Feedback.iterate (trace : G.Feedback) {U B : K} (f : U ⟶ P.sum B U)
    (hf : G.guarded f) : U ⟶ B :=
  trace (P.desc f f) (by
    change G.guarded (P.inr ≫ P.desc f f)
    simpa using hf)

/-- Retarget the incoming and outgoing non-feedback interfaces. -/
def tighten {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') : P.sum A' U ⟶ P.sum B' U :=
  P.map a (𝟙 U) ≫ f ≫ P.map b (𝟙 U)

/-- Place an independent computation beside the entry and result of a feedback body. -/
def superpose {A B U A' B' : K} (f : P.sum A U ⟶ P.sum B U) (g : A' ⟶ B') :
    P.sum (P.sum A A') U ⟶ P.sum (P.sum B B') U :=
  P.desc
    (P.desc (P.inl ≫ f ≫ P.map P.inl (𝟙 U)) (g ≫ P.inr ≫ P.inl))
    (P.inr ≫ f ≫ P.map P.inl (𝟙 U))

end Guardedness

end Silmaril.Calco2019
