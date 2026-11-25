module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Thms

/-! # Superposition in the four-interface trace profile -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- Exchange the two middle entries of a fourfold coproduct. -/
def exchangeMiddle (P : Coproducts K) {A B C D : K} :
    P.sum (P.sum A B) (P.sum C D) ⟶ P.sum (P.sum A C) (P.sum B D) :=
  P.desc (P.desc (P.inl ≫ P.inl) (P.inl ≫ P.inr))
    (P.desc (P.inr ≫ P.inl) (P.inr ≫ P.inr))

/-- Place an independent map beside a trace body. The two marked inputs and
the two marked outputs are joined by coproduct, with feedback still only on
the original body. -/
def traceSuperpose {A B C D U A' B' C' D' : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U))
    (g : P.sum A' B' ⟶ P.sum C' D') :
    P.sum (P.sum (P.sum A A') U) (P.sum B B') ⟶
      P.sum (P.sum C C') (P.sum (P.sum D D') U) :=
  restoreTraceBody (tighten (superpose (traceBody f) g) (exchangeMiddle P) (exchangeMiddle P))

end Silmaril.Calco2019.Guardedness
