module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Defs

/-! # Guarded packing, decoding and substitution in the joined quotient -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPacking

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)
open Paper.WithProjectionReturnsAndUnitEta (Step projection)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "E" => Paper.Extension.Eqv (Seed)
local notation "Obj" => ofType (Seed)

theorem unpack_pack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r L) : E Γ (decode L r.packExits) r L :=
  .paper (.cfgEta (.native hr.unpack_packExits))

theorem pack_unpack {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r [packedExitType L]) : E Γ (decode L r).packExits r [packedExitType L] :=
  .paper (.cfgEta (.native hr.pack_unpackExits))

theorem pack_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) (h : E Γ r s L) :
    E Γ r.packExits s.packExits [packedExitType L] :=
  .lsubstPost h hr hs (fun _ _ hi => (packExits_valueFamily (Φ := Φ) Γ L hi).hasType)

theorem decode_congr {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r [packedExitType L]) (hs : ValueBranches Γ s [packedExitType L])
    (h : E Γ r s [packedExitType L]) : E Γ (decode L r) (decode L s) L :=
  .lsubstPost h hr hs (fun _ _ hi => (unpackExits_valueFamily (Φ := Φ) Γ L hi).hasType)

theorem pack_eqv_iff {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    E Γ r.packExits s.packExits [packedExitType L] ↔ E Γ r s L :=
  ⟨fun h => .trans (.symm (unpack_pack hr)) (.trans (decode_congr hr.packExits hs.packExits h) (unpack_pack hs)),
    pack_congr hr hs⟩

theorem packArrow_eq_iff {A : τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches [A] r L) (hs : ValueBranches [A] s L) :
    packArrow hr = packArrow hs ↔ E [A] r s L :=
  (ofRegion_eq_iff (Seed) hr.packExits hs.packExits).trans (pack_eqv_iff hr hs)

set_option backward.isDefEq.respectTransparency false in
theorem packClass_bijective (A : τ) (L : LCtx τ) :
    Function.Bijective (packClass (Φ := Φ) (A := A) (L := L)) := by
  constructor
  · intro r s
    refine Quot.inductionOn r ?_
    intro r
    refine Quot.inductionOn s ?_
    intro s h
    exact Quot.sound ((packArrow_eq_iff r.property s.property).1 h)
  · intro f
    obtain ⟨g, rfl⟩ := (projection (τ := τ) (Φ := Φ)).map_surjective f
    obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion g
    refine ⟨regionClass (decode_valueBranches hr), ?_⟩
    exact (ofRegion_eq_iff (Seed) (decode_valueBranches hr).packExits hr).2 (pack_unpack hr)

theorem pack_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches Γ r L) (hσ : LSubst.ValueFamily Γ L K σ) :
    E Γ (r.lsubst σ).packExits (r.packExits.lsubst (fun _ => packedContinuation L σ)) [packedExitType K] := by
  have substituted : E Γ (r.lsubst σ) ((decode L r.packExits).lsubst σ) K :=
    .lsubstPost (unpack_pack hr).symm hr (decode_valueBranches hr.packExits) (fun _ _ hi => (hσ hi).hasType)
  have h := pack_congr (hr.lsubst hσ) ((decode_valueBranches hr.packExits).lsubst hσ) substituted
  let dec : Nat → Region Φ := fun _ => unpackExits L
  let tag : Nat → Region Φ := fun i => .br 0 (packedExitArg i (.var 0))
  have repack :
      ((decode L r.packExits).lsubst σ).packExits =
        r.packExits.lsubst (fun _ => packedContinuation L σ) := by
    change ((r.packExits.lsubst dec).lsubst σ).lsubst tag = _
    rw [lsubst_comp (r.packExits.lsubst dec), lsubst_comp r.packExits]
    rfl
  exact repack ▸ h

theorem packArrow_lsubst {A : τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches [A] r L) (hσ : LSubst.ValueFamily [A] L K σ) :
    packArrow (hr.lsubst hσ) =
      ofRegion (Seed) (hr.packExits.lsubst (packedContinuation_valueFamily hσ)) :=
  (ofRegion_eq_iff (Seed) _ _).2 (pack_lsubst hr hσ)


omit [TypeFormers τ] [HasTy Φ τ] in
private theorem unpackExits_lift (L : LCtx τ) (ρ : Nat → Nat) :
    (unpackExits L : Region Φ).renameVars (Silmaril.DeBruijn.lift ρ) = unpackExits L := by
  induction L generalizing ρ with
  | nil => rfl
  | cons A L ih =>
    simp only [unpackExits, renameVars, Tm.rename, renameVars_renameLabels, ih]
    rfl

private theorem packedArg_lift (i : Nat) (ρ : Nat → Nat) :
    (packedExitArg i (.var 0 : Tm Φ)).rename (Silmaril.DeBruijn.lift ρ) = packedExitArg i (.var 0) := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [packedExitArg, Tm.rename, ih]

omit [TypeFormers τ] [HasTy Φ τ] in
private theorem packedContinuation_lift (L : LCtx τ) (σ : Nat → Region Φ) :
    packedContinuation L (liftLSubstVars σ) =
      (packedContinuation L σ).renameVars (Silmaril.DeBruijn.lift Nat.succ) := by
  let dec : Nat → Region Φ := fun _ => unpackExits L
  let tag : Nat → Region Φ := fun i => .br 0 (packedExitArg i (.var 0))
  have d : liftLSubstVars dec = dec := funext (fun _ => unpackExits_lift L Nat.succ)
  have t : liftLSubstVars tag = tag := by
    funext i
    exact congrArg (Region.br 0) (packedArg_lift i Nat.succ)
  have h : compLSubst dec (compLSubst (liftLSubstVars σ) tag) =
      liftLSubstVars (compLSubst dec (compLSubst σ tag)) := by
    calc
      _ = compLSubst (liftLSubstVars dec) (compLSubst (liftLSubstVars σ) (liftLSubstVars tag)) := by rw [d, t]
      _ = _ := by rw [compLSubst_liftVars, compLSubst_liftVars]
  exact congrFun h 0

theorem packArrow_comp {A : τ} {L K : LCtx τ} {r : Region Φ} {σ : Nat → Region Φ}
    (hr : ValueBranches [A] r L) (hσ : LSubst.ValueFamily [] L K σ) :
    packArrow (hr.lsubst (hσ.liftVars A)) =
      packArrow hr ≫ ofRegion (Seed) (packedContinuation_typed hσ) := by
  have typed : ValueBranches [A]
      (compLSubst (fun _ => r.packExits) (fun _ => packedContinuation L σ) 0) [packedExitType K] :=
    hr.packExits.lsubst ((packedContinuation_valueFamily hσ).liftVars A)
  change _ = (projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion hr.packExits) ≫
    (projection (τ := τ) (Φ := Φ)).map (Paper.TypeCategory.ofRegion (packedContinuation_typed hσ))
  rw [← Functor.map_comp, Paper.TypeCategory.ofRegion_comp _ _ typed]
  apply (ofRegion_eq_iff (Seed) _ _).2
  have h := pack_lsubst hr (hσ.liftVars A)
  rw [packedContinuation_lift] at h
  exact h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedExitPacking
