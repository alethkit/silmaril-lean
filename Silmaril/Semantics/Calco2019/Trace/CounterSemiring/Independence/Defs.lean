module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.MatrixTrace.Thms
public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Witness.Thms
public import Silmaril.Semantics.Calco2019.Trace.PointedCpo.Defs

/-! # The binary cycle identity and its finite matrix instance -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

/-- Run the body from either copy, with recursion entering the other copy. -/
def binaryCycleBody {X Y : K} (f : X ⟶ P.sum Y X) : P.sum X X ⟶ P.sum Y (P.sum X X) :=
  P.desc (f ≫ P.map (𝟙 Y) P.inr) (f ≫ P.map (𝟙 Y) P.inl)

/-- The commutative identity of the deterministic two-state cycle. -/
def Fixpoints.BinaryCycleIdentity (F : G.Fixpoints) : Prop :=
  ∀ {X Y : K} (f : X ⟶ P.sum Y X)
    (hf : G.guarded f) (hc : G.guarded (binaryCycleBody f)),
    F.iterate (binaryCycleBody f) hc = P.desc (𝟙 X) (𝟙 X) ≫ F.iterate f hf

end Silmaril.Calco2019.Guardedness

namespace Silmaril.Calco2019.CounterSemiring.FiniteMatrix

open CategoryTheory

/-- One state and one possible exit, with the nonidentity generator on recursion. -/
def one : Object.{0} := ⟨Unit⟩

def oneBody : one ⟶ coproducts.sum one one := Matrix.of singleLoop

end Silmaril.Calco2019.CounterSemiring.FiniteMatrix

namespace Silmaril.Calco2019.PointedCpo

open OmegaCompletePartialOrder

/-- At each state, apply the original continuous equation to the other state. -/
def alternating {D : Type u} [OmegaCompletePartialOrder D] (f : D →𝒄 D) :
    (Bool → D) →𝒄 (Bool → D) where
  toFun xs i := f (xs (!i))
  monotone' _ _ h i := f.monotone (h (!i))
  map_ωSup' chain := by
    funext i
    exact f.continuous (chain.map ⟨fun xs => xs (!i), fun _ _ h => h (!i)⟩)

end Silmaril.Calco2019.PointedCpo
