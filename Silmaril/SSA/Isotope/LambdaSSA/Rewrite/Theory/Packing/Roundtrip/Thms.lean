module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.PackingRoundtrip

/-! # Syntactic retraction of the packed exit interface -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory

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

theorem packExits_valueFamily (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily Γ L [packedExitType L] (fun ℓ => .br 0 (packedExitArg ℓ (.var 0 : Tm Φ))) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_valueFamily Γ L

theorem unpackExits_valueFamily (Γ : VCtx τ) (L : LCtx τ) :
    LSubst.ValueFamily Γ [packedExitType L] L (fun _ => unpackExits L : Nat → Region Φ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.unpackExits_valueFamily Γ L

/-- Decoding and repacking an empty-typed input is the identity at its
singleton exit interface, by native initiality. -/
theorem unpackExits_empty_packExits (Γ : VCtx τ) :
    SubstitutionEquiv ((Silmaril.empty : τ) :: Γ) (unpackExits ([] : LCtx τ) : Region Φ).packExits
      (.br 0 (.var 0)) [Silmaril.empty] :=
  .initial_var (i := 0) rfl (unpackExits_hasType Γ []).packExits (.br rfl (.var rfl))

/-- The tagged exit interface admits a split inclusion in the native
continuation category. -/
theorem ContinuationContext.exists_packed_retraction {Γ : VCtx τ} (X : ContinuationContext Φ Γ) :
    ∃ (pack : X ⟶ (⟨[packedExitType X.labels]⟩ : ContinuationContext Φ Γ))
      (unpack : (⟨[packedExitType X.labels]⟩ : ContinuationContext Φ Γ) ⟶ X),
      pack ≫ unpack = 𝟙 X :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.exists_packed_retraction X

/-- Packing reflects native rewrite equivalence on regions with value branches. -/
theorem ValueBranches.packExits_equiv_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    SubstitutionEquiv Γ r.packExits s.packExits [packedExitType L] ↔ SubstitutionEquiv Γ r s L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packExits_equiv_iff hr hs

end Silmaril.Isotope.LambdaSSA.Region
