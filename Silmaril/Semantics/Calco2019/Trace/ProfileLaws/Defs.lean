module

public import Silmaril.Semantics.Calco2019.Trace.ProfileConverse.Thms
public import Silmaril.Semantics.Calco2019.Trace.ProfileSliding.Thms
public import Silmaril.Semantics.Calco2019.Trace.ProfileSuperpose.Thms
public import Silmaril.Semantics.Calco2019.Trace.ProfileUnits.Thms

/-! # Equations for an arbitrary four-interface guarded trace operator -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.FourInterfaceTrace

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- The seven laws of Figure 4 other than Vanishing II. -/
structure LocalLaws (T : G.FourInterfaceTrace) : Prop where
  tighten : T.Tightening
  superpose {A B C D U A' B' C' D' : K}
    {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
    {g : P.sum A' B' ⟶ P.sum C' D'} (hf : G.TraceGuard f) (hg : G.guarded (P.inl ≫ g)) :
    T.run (traceSuperpose_guard hf hg) =
      exchangeMiddle P ≫ P.map (T.run hf) g ≫ exchangeMiddle P
  vanishInitial {A B C D I : K} (i : IsInitial I)
    {f : P.sum (P.sum A I) B ⟶ P.sum C (P.sum D I)} (hf : G.TraceGuard f) :
    T.run hf = deleteInitialFeedback i f
  yank {I U : K} (i : IsInitial I) :
    T.run (traceInterchange_guard (G := G) (U := U) i) =
      P.desc (i.to U) (𝟙 U) ≫ (P.inl : U ⟶ P.sum U I)
  slideI {A B C D E H U V I : K} (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum E I) (P.sum C D) (P.sum H I) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first)) (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second)) :
    T.run (s.slidingI_guards i ha hu he).1 = T.run (s.slidingI_guards i ha hu he).2
  slideII {A B C D F J U V I : K} (i : IsInitial I)
    (s : TwoBody P (P.sum A B) (P.sum I F) (P.sum C D) (P.sum I J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first)) (hu : G.nested (P.inr ≫ s.first))
    (hv : G.guarded ((P.inr ≫ s.second) ≫ externalMark)) :
    T.run (s.slidingII_guards i ha hu hv).1 = T.run (s.slidingII_guards i ha hu hv).2
  slideIII {A B C D E F H J U V : K}
    (s : TwoBody P (P.sum A B) (P.sum E F) (P.sum C D) (P.sum H J) U V)
    (ha : G.nested (P.inl ≫ P.inl ≫ s.first)) (hu : G.nested (P.inr ≫ s.first))
    (he : G.nested (P.inl ≫ P.inl ≫ s.second)) (hv : G.nested (P.inr ≫ s.second)) :
    T.run (s.slidingIII_guards ha hu he hv).1 = T.run (s.slidingIII_guards ha hu he hv).2

end Silmaril.Calco2019.Guardedness.FourInterfaceTrace
