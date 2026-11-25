module

public import Silmaril.Semantics.Calco2019.Trace.Equivalence.Thms

/-! # Ordinary monoidal trace on a co-Cartesian category -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness.Feedback

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- Split a total trace body on a coproduct of two feedback objects. -/
def splitTotalBody {A B U V : K} (f : P.sum A (P.sum U V) ⟶ P.sum B (P.sum U V)) :
    TwoStateBody (Guardedness.greatest P) A B U V where
  entry := P.inl ≫ f ≫ P.assocInv
  first := P.inl ≫ P.inr ≫ f ≫ P.assocInv
  second := P.inr ≫ P.inr ≫ f ≫ P.assocInv
  guarded := True.intro

/-- The Joyal–Street–Verity trace equations for coproduct as tensor.
Dinaturality slides an ordinary map between feedback objects.
Vanishing II uses the actual inner trace as the outer trace body. -/
structure JoyalStreetVerity (tr : Guardedness.Feedback (Guardedness.greatest P)) : Prop where
  tighten : Tightening tr
  superpose : Superposition tr
  slide {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (q : V ⟶ U) :
    tr (f ≫ P.map (𝟙 B) q) True.intro = tr (P.map (𝟙 A) q ≫ f) True.intro
  vanishInitial {A B I : K} (i : IsInitial I) (f : P.sum A I ⟶ P.sum B I) :
    tr f True.intro = P.inl ≫ f ≫ P.desc (𝟙 B) (i.to B)
  vanishPair {A B U V : K} (s : TwoStateBody (Guardedness.greatest P) A B U V) :
    onBranches tr (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc) True.intro =
      tr (onBranches tr (P.desc s.entry s.first) s.second True.intro) True.intro
  yank (U : K) : tr (P.swap (X := U) (Y := U)) True.intro = 𝟙 U

end Silmaril.Calco2019.Guardedness.Feedback
