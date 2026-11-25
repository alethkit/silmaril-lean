module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackingRoundtrip

/-! # Syntactic retraction of the packed exit interface -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Decoding a constructor-valued tagged payload rewrites to its original
branch, by case β and constructor-value let β. -/
theorem unpackExits_packedArg {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {A : τ} {a : Tm Φ}
    (hℓ : At L ℓ A) (ha : Tm.BranchValue Γ a A) :
    SubstitutionEquiv Γ ((unpackExits L).substVars (Tm.singleSubst (packedExitArg ℓ a))) (.br ℓ a) L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackExits_packedArg hℓ ha

/-- Packing and decoding the exits is a native rewrite of the original
region at all exactly typed constructor-valued branch arguments. -/
theorem ValueBranches.unpack_packExits {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) :
    SubstitutionEquiv Γ (r.packExits.lsubst (fun _ => unpackExits L)) r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpack_packExits hr

/-- For arbitrary typed branch arguments, bind each argument once before
packing and decoding the exits. -/
theorem HasType.unpack_packExits_afterBinding {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : HasType Γ r L) :
    SubstitutionEquiv Γ (r.bindBranchArguments.packExits.lsubst (fun _ => unpackExits L))
      r.bindBranchArguments L :=
  hr.bindBranchArguments.unpack_packExits

end Silmaril.Isotope.LambdaSSA.Region
