module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! Check exit packing on an abstract two-label interface. The packed input is
a variable, so decoding its outer and inner sums uses the native sum equation. -/

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region

namespace LambdaSSANeutralPacking

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Exercise the public inverse on the smallest interface with two distinct label indices. -/
theorem neutralPacking {Γ : VCtx τ} (A B : τ) :
    let P := packedExitType [A, B]
    SubstitutionEquiv (P :: Γ)
      (((Region.br 0 (.var 0) : Region Φ).lsubst (fun _ => unpackExits [A, B])).packExits)
      (.br 0 (.var 0)) [P] :=
  ValueBranches.pack_unpackExits (L := [A, B]) (.br rfl (.var rfl))

/-- The same equality follows directly from two sum rewrites and the empty case. -/
theorem neutralPacking_by_rules {Γ : VCtx τ} (A B : τ) :
    let P := packedExitType [A, B]
    SubstitutionEquiv (P :: Γ)
      (((Region.br 0 (.var 0) : Region Φ).lsubst (fun _ => unpackExits [A, B])).packExits)
      (.br 0 (.var 0)) [P] := by
  let Q := Silmaril.coprod B (Silmaril.empty : τ)
  let P := Silmaril.coprod A Q
  let dead : Region Φ := unpackExits ([] : LCtx τ)
  change SubstitutionEquiv (P :: Γ)
    (.case (.var 0) (.br 0 (.inl (.var 0)))
      (.case (.var 0) (.br 0 (.inr (.inl (.var 0)))) dead))
    (.br 0 (.var 0)) [P]
  have deadTyped : Region.HasType (Silmaril.empty :: Q :: P :: Γ) dead [P] :=
    .cfg (fun _ : Fin 1 => Silmaril.empty) (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl))
  have emptyArm : SubstitutionEquiv (Silmaril.empty :: Q :: P :: Γ) dead
      (.br 0 (.inr (.inr (.var 0)))) [P] :=
    .initial_var (i := 0) rfl deadTyped (.br rfl (.inr (.inr (.var rfl))))
  have innerLeft : Region.HasType (B :: Q :: P :: Γ)
      (.br 0 (.inr (.inl (.var 0))) : Region Φ) [P] :=
    .br rfl (.inr (.inl (.var rfl)))
  have innerBody : Region.HasType (Q :: Q :: P :: Γ) (.br 0 (.inr (.var 0)) : Region Φ) [P] :=
    .br rfl (.inr (.var rfl))
  have innerCongr := SubstitutionEquiv.case
    (Tm.HasType.var (Φ := Φ) (Γ := Q :: P :: Γ) (i := 0) (A := Q) rfl)
    (.base (.refl innerLeft)) emptyArm
  have innerEta := SubstitutionEquiv.caseValue (A := B) (B := Silmaril.empty)
    (Tm.BranchValue.var (Φ := Φ) (Γ := Q :: P :: Γ) (i := 0) (A := Q) rfl) innerBody
  have outerLeft : Region.HasType (A :: P :: Γ) (.br 0 (.inl (.var 0)) : Region Φ) [P] :=
    .br rfl (.inl (.var rfl))
  have outerBody : Region.HasType (P :: P :: Γ) (.br 0 (.var 0) : Region Φ) [P] :=
    .br rfl (.var rfl)
  have outerCongr := SubstitutionEquiv.case
    (Tm.HasType.var (Φ := Φ) (Γ := P :: Γ) (i := 0) (A := P) rfl)
    (.base (.refl outerLeft)) (innerCongr.trans innerEta)
  exact outerCongr.trans (SubstitutionEquiv.caseValue (A := A) (B := Q)
    (Tm.BranchValue.var (Φ := Φ) (Γ := P :: Γ) (i := 0) (A := P) rfl) outerBody)

end LambdaSSANeutralPacking
