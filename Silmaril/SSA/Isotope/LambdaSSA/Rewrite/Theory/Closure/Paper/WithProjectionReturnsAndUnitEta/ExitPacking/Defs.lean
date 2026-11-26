module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.CfgEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms

/-! # Finite exit packing in the projection-return and unit-η quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking

open Silmaril Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "E" => Paper.Extension.Eqv (Seed)
local notation "Obj" => ofType (Seed)

/-- Substitute the finite tagged-sum decoder at the singleton exit. -/
def decode (L : LCtx τ) (r : Region Φ) : Region Φ :=
  r.lsubst (fun _ => unpackExits L)

theorem decode_valueBranches {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (hr : ValueBranches Γ r [packedExitType L]) : ValueBranches Γ (decode L r) L :=
  hr.lsubst (unpackExits_valueFamily Γ L)

/-- Decode the source tag, substitute its continuation, and tag the result.
The two compositions retain the original source captures. -/
def packedContinuation (L : LCtx τ) (σ : Nat → Region Φ) : Region Φ :=
  compLSubst (fun _ => unpackExits L) (compLSubst σ (fun i => .br 0 (packedExitArg i (.var 0)))) 0

/-- The packed continuation is a guarded singleton continuation family. -/
theorem packedContinuation_valueFamily {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) :
    LSubst.ValueFamily Γ [packedExitType L] [packedExitType K] (fun _ => packedContinuation L σ) :=
  (unpackExits_valueFamily Γ L).comp (hσ.comp (packExits_valueFamily Γ K))

theorem packedContinuation_typed {Γ : VCtx τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily Γ L K σ) :
    ValueBranches (packedExitType L :: Γ) (packedContinuation L σ) [packedExitType K] :=
  (packedContinuation_valueFamily hσ) (ℓ := 0) rfl

/-- The joined singleton arrow obtained by tagging the outward branches. -/
def packArrow {A : τ} {L : LCtx τ} {r : Region Φ} (hr : ValueBranches [A] r L) :
    Obj A ⟶ Obj (packedExitType L) :=
  ofRegion (Seed) hr.packExits

/-- Guarded regions at a fixed singleton input and typed exit list, modulo
the same contextual joined equations used on singleton arrows. -/
abbrev RegionClass (A : τ) (L : LCtx τ) :=
  Quot (fun r s : {r : Region Φ // ValueBranches [A] r L} => E [A] r.val s.val L)

def regionClass {A : τ} {L : LCtx τ} {r : Region Φ} (hr : ValueBranches [A] r L) : RegionClass (Φ := Φ) A L :=
  Quot.mk _ ⟨r, hr⟩

/-- Tag the exits without choosing a representative of the region class. -/
def packClass {A : τ} {L : LCtx τ} (r : RegionClass (Φ := Φ) A L) :
    Obj A ⟶ Obj (packedExitType L) :=
  Quot.liftOn r (fun h => packArrow h.property) (fun r s h =>
    (ofRegion_eq_iff (Seed) _ _).2
      (.lsubstPost h r.property s.property (fun _ _ hi => (packExits_valueFamily (Φ := Φ) [A] L hi).hasType)))

/-- Apply a guarded continuation family to a joined region class. -/
def substitute {A : τ} {L K : LCtx τ} {σ : Nat → Region Φ}
    (hσ : LSubst.ValueFamily [A] L K σ) (r : RegionClass (Φ := Φ) A L) : RegionClass (Φ := Φ) A K :=
  Quot.liftOn r (fun p => regionClass (p.property.lsubst hσ))
    (fun p q h => Quot.sound (.lsubstPost h p.property q.property (fun _ _ hi => (hσ hi).hasType)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.ExitPacking
