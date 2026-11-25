module

public import Silmaril.Semantics.Calco2019.Trace.Defs

/-! # The four-interface guarded trace profile cited in Remark 15 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

/-- A guarded trace body has inputs `(A + U) + B` and outputs `C + (D + U)`.
Its restriction to `A + U` is guarded in `D + U`. -/
def TraceGuard (G : Guardedness P) {A B C D U : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)) : Prop :=
  G.guarded (P.inl ≫ f)

/-- Present the same body with the feedback state last and with a single result object. -/
def traceBody {A B C D U : K}
    (f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)) :
    P.sum (P.sum A B) U ⟶ P.sum (P.sum C D) U :=
  P.desc (P.desc (P.inl ≫ P.inl ≫ f ≫ P.assocInv) (P.inr ≫ f ≫ P.assocInv))
    (P.inr ≫ P.inl ≫ f ≫ P.assocInv)

end Silmaril.Calco2019.Guardedness
