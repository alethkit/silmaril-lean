module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPacking

/-! # The joined quotient round trip for a finite typed exit list -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "E" => Paper.Extension.Eqv (Seed)
local notation "Obj" => ofType (Seed)

/-- Decoding a tagged region recovers its original representative modulo the joined rules. -/
theorem unpack_pack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : E Γ (decode L r.packExits) r L :=
  JoinedExitPacking.unpack_pack hr

/-- Decoding and repacking a guarded singleton region recovers its representative. -/
theorem pack_unpack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r [packedExitType L]) : E Γ (decode L r).packExits r [packedExitType L] :=
  JoinedExitPacking.pack_unpack hr

/-- Packing preserves and reflects the joined rewrite relation at fixed guarded interfaces. -/
theorem pack_eqv_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    E Γ r.packExits s.packExits [packedExitType L] ↔ E Γ r s L :=
  JoinedExitPacking.pack_eqv_iff hr hs

/-- Equality of the packed singleton arrows is exactly joined region equivalence. -/
theorem packArrow_eq_iff {A : τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    packArrow hr = packArrow hs ↔ E [A] r s L :=
  JoinedExitPacking.packArrow_eq_iff hr hs

theorem packClass_bijective (A : τ) (L : LCtx τ) :
    Function.Bijective (packClass (Φ := Φ) (A := A) (L := L)) :=
  JoinedExitPacking.packClass_bijective A L

/-- A guarded multi-exit region class with a singleton input is equivalent to
a joined singleton arrow into the exact tagged sum. -/
@[expose] noncomputable def packEquiv (A : τ) (L : LCtx τ) :
    RegionClass (Φ := Φ) A L ≃ (Obj A ⟶ Obj (packedExitType L)) :=
  Equiv.ofBijective packClass (packClass_bijective A L)

theorem packEquiv_apply {A : τ} {L : LCtx τ} {r : Region Φ} (hr : ValueBranches [A] r L) :
    packEquiv A L (regionClass hr) = packArrow hr :=
  rfl

theorem packEquiv_symm_ofRegion {A : τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches [A] r [packedExitType L]) :
    (packEquiv A L).symm (ofRegion (Seed) hr) = regionClass (decode_valueBranches hr) := by
  apply (packEquiv (Φ := Φ) A L).injective
  rw [Equiv.apply_symm_apply, packEquiv_apply]
  exact ((ofRegion_eq_iff (Seed) (decode_valueBranches hr).packExits hr).2 (pack_unpack hr)).symm

/-- Packing commutes with guarded continuation substitution, including families
whose arms refer to the retained source context. -/
theorem pack_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches Γ r L) (hσ : LSubst.ValueFamily Γ L K σ) :
    E Γ (r.lsubst σ).packExits (r.packExits.lsubst (fun _ => packedContinuation L σ)) [packedExitType K] :=
  JoinedExitPacking.pack_lsubst hr hσ

/-- The captured substitution square gives equality in the joined singleton category. -/
theorem packArrow_lsubst {A : τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches [A] r L) (hσ : LSubst.ValueFamily [A] L K σ) :
    packArrow (hr.lsubst hσ) =
      ofRegion (Seed) (hr.packExits.lsubst (packedContinuation_valueFamily hσ)) :=
  JoinedExitPacking.packArrow_lsubst hr hσ

/-- With empty captures, the packed continuation is an ordinary singleton
arrow, and guarded substitution becomes categorical composition. -/
theorem packArrow_comp {A : τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches [A] r L) (hσ : LSubst.ValueFamily [] L K σ) :
    packArrow (hr.lsubst (hσ.liftVars A)) =
      packArrow hr ≫ ofRegion (Seed) (packedContinuation_typed hσ) :=
  JoinedExitPacking.packArrow_comp hr hσ

/-- Substitution on region classes depends only on the joined class of each continuation. -/
theorem substitute_congr {A : τ} {L K : LCtx τ} {σ υ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily [A] L K σ) (hυ : LSubst.ValueFamily [A] L K υ)
    (h : ∀ ⦃i B⦄, At L i B → E (B :: [A]) (σ i) (υ i) K) :
    substitute hσ = substitute hυ :=
  funext fun q => Quot.inductionOn q (fun p => Quot.sound (.lsubstCongr p.property h))

/-- The quotient packing equivalence takes substitution by a capture-free
family to postcomposition with its packed joined arrow. -/
theorem packEquiv_substitute {A : τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily [] L K σ) (q : RegionClass (Φ := Φ) A L) :
    packEquiv A K (substitute (hσ.liftVars A) q) =
      packEquiv A L q ≫ ofRegion (Seed) (packedContinuation_typed hσ) :=
  Quot.inductionOn q (fun p => packArrow_comp p.property hσ)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking
