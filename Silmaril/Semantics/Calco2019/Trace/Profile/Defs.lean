module

public import Silmaril.Semantics.Calco2019.Trace.Guarded.Thms
public import Silmaril.Semantics.Calco2019.Trace.Thms

/-! # Comparing four-interface traces and coproduct feedback -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- Put the feedback input between the two external inputs and mark the second
external output together with the feedback output. -/
def restoreTraceBody {A B C D U : K}
    (f : P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U) :
    P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U) :=
  P.desc (P.desc (P.inl ≫ P.inl ≫ f ≫ P.assoc) (P.inr ≫ f ≫ P.assoc))
    (P.inr ≫ P.inl ≫ f ≫ P.assoc)

/-- The guard on a normalized four-interface body. Both the first
external input and the feedback input are guarded in the two marked outputs. -/
def ProfileGuard (G : Guardedness P) {A B C D U : K}
    (f : P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U) : Prop :=
  G.nested (P.inl ≫ P.inl ≫ f) ∧ G.nested (P.inr ≫ f)

/-- Tighten the external interfaces of a four-interface body. -/
def traceTighten {A B C D U A' B' C' D' : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U))
    (a : P.sum A' B' ⟶ P.sum A B) (b : P.sum C D ⟶ P.sum C' D') :
    P.sum (P.sum A' U) B' ⟶ P.sum C' (P.sum D' U) :=
  restoreTraceBody (tighten (traceBody f) a b)

end Silmaril.Calco2019.Guardedness
