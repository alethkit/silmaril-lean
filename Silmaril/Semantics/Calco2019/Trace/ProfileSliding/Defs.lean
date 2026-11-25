module

public import Silmaril.Semantics.Calco2019.Trace.Profile.Thms
public import Silmaril.Semantics.Calco2019.Trace.TwoBody.Thms

/-! # Sliding with separate marked and unmarked interfaces -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

namespace TwoBody

variable {A B C D E F H J U V : K}
  (s : TwoBody P (P.sum A B) (P.sum E F) (P.sum C D) (P.sum H J) U V)

/-- Pair the marked inputs from both bodies, followed by the unmarked inputs. -/
def slideEntry : P.sum (P.sum A E) (P.sum B F) ⟶ P.sum (P.sum A B) (P.sum E F) :=
  P.desc (P.map P.inl P.inl) (P.map P.inr P.inr)

/-- Pair the unmarked outputs from both bodies, followed by the marked outputs. -/
def slideExit : P.sum (P.sum C D) (P.sum H J) ⟶ P.sum (P.sum C H) (P.sum D J) :=
  P.desc (P.map P.inl P.inl) (P.map P.inr P.inr)

/-- Display the marked interfaces when the loop is cut before the first body. -/
def markedCutFirst : P.sum (P.sum (P.sum A E) U) (P.sum B F) ⟶
    P.sum (P.sum C H) (P.sum (P.sum D J) U) :=
  restoreTraceBody (tighten s.cutFirst slideEntry slideExit)

/-- Display the marked interfaces when the loop is cut before the second body. -/
def markedCutSecond : P.sum (P.sum (P.sum A E) V) (P.sum B F) ⟶
    P.sum (P.sum C H) (P.sum (P.sum D J) V) :=
  restoreTraceBody (tighten s.cutSecond slideEntry slideExit)

end TwoBody

/-- Move the recursive output to the unmarked side, retaining the marked
external output. This is the output marking of the second body in Sliding II. -/
def externalMark {C D U : K} : P.sum (P.sum C D) U ⟶ P.sum (P.sum C U) D :=
  P.desc (P.map P.inl (𝟙 D)) (P.inr ≫ P.inl)

end Silmaril.Calco2019.Guardedness
