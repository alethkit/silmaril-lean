module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentPoint

/-! # Mixed tables: completeness at the original entries, and the regression -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)

/-! ## Completeness -/

section Complete

variable {M M' : Nat} {r r' : Region signature.Instr} {L : Bool → Landing M} {L' : Bool → Landing M'}

/-- Loops with landings are equal exactly when their landings agree at
each constant. -/
theorem landed_iff_rel (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L') : Eqv false [State] r r' [Bit] ↔ ∀ q, (L q).Rel (L' q) :=
  ⟨fun e q => TableModel.landed_rel h h' hl hl'
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) q,
    landed_eqv h h' hl hl'⟩

/-- And exactly when they are valid in every supported model. -/
theorem landed_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : Landed r L) (hl' : Landed r' L') : Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => landed_eqv h h' hl hl' (TableModel.landed_rel h h' hl hl' v)⟩

/-- Landings transfer along an equation of the quotient. -/
theorem landed_congr (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (e : Eqv false [State] r r' [Bit]) (hl : Landed r' L) : Landed r L := fun q =>
  (Paper.Extension.Eqv.trans
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h) (constEntry_typed q h')).1
      ((q_const q h).trans ((congrArg (QLit (const_typed q) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N h h').2 e)).trans (q_const q h').symm))) (hl q))

end Complete

/-! ## The written table -/

section Written

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {rank : Fin (K + 1) → Bool → Nat} {fuel : Nat} (hr : Ranked row act rank fuel)

theorem mix_written_eqv (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) ((mixRouter row act).entered j) [Bit] :=
  .paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mix_written_arrow row act j))

include hr in
theorem written_landed (j : Fin (K + 1)) :
    Landed ((mixWritten row act).entered j) (mixLanding row act fuel j) :=
  landed_congr ((mixWritten row act).entered_typed j) ((mixRouter row act).entered_typed j)
    (mix_written_eqv row act j) (mix_landed row act hr j)

include hr in
theorem written_case (j : Fin (K + 1)) :
    Eqv false [State] ((mixWritten row act).entered j) (mixCase row act fuel j) [Bit] :=
  landed_case ((mixWritten row act).entered_typed j) (written_landed row act hr j)

end Written

/-! ## Regression -/

theorem hop_ranked (l f s : Bool) : Ranked (hopRow l) (hopAct f s) hopRank 3 := by
  refine ⟨fun i g => ?_, fun i g e hrow j q hact e' hrow' => ?_⟩
  · match i with
    | 0 => exact Nat.lt_succ_self 2
    | 1 => exact Nat.lt_succ_of_lt (Nat.lt_succ_self 1)
    | 2 => exact Nat.succ_pos 2
  · match i with
    | 0 =>
      cases hrow
      cases hact
      exact Nat.lt_succ_self 1
    | 1 =>
      cases hrow
      cases g
      · cases hact
      · cases hact
        cases hrow'
    | 2 => cases hrow

/-- A silent cycle has no ranking. -/
theorem spin_not_ranked (rank : Fin 1 → Bool → Nat) (fuel : Nat) : ¬ Ranked spinRow spinAct rank fuel :=
  fun h => Nat.lt_irrefl _ (h.2 0 false 1 rfl 0 false rfl 1 rfl)

/-- Entered with `true`, two silent hops reach a return. -/
theorem hop_return (l : Bool) : mixLanding (hopRow l) (hopAct true true) 3 0 true = .ret true := by
  rfl

/-- Entered with `false`, two silent hops change the Bit and reach the
request row with `true`. -/
theorem hop_request (l : Bool) :
    mixLanding (hopRow l) (hopAct true true) 3 0 false =
      .at (mixSource (hopRow l) (hopAct true true) 3) (splitIdx 2 true) true := by
  rfl

/-- The tables are equal at the first row exactly when the hop changes
the Bit in the same way and the request row is entered with the same Bit. -/
theorem hop_eqv_iff (l f s f' s' : Bool) :
    Eqv false [State] ((mixWritten (hopRow l) (hopAct f s)).entered 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered 0) [Bit] ↔ f = f' ∧ s = s' := by
  constructor
  · intro e
    have h := (landed_iff_rel ((mixWritten (hopRow l) (hopAct f s)).entered_typed 0)
      ((mixWritten (hopRow l) (hopAct f' s')).entered_typed 0)
      (written_landed (hopRow l) (hopAct f s) (hop_ranked l f s) 0)
      (written_landed (hopRow l) (hopAct f' s') (hop_ranked l f' s') 0)).1 e
    cases f <;> cases f' <;> cases s <;> cases s' <;> first
      | exact ⟨rfl, rfl⟩
      | exact False.elim (h true)
      | exact absurd (And.left (h true)) (by decide)
      | exact absurd (And.left (h false)) (by decide)
  · rintro ⟨rfl, rfl⟩
    exact Paper.Extension.Eqv.refl ((mixWritten (hopRow l) (hopAct f s)).entered_typed 0).hasType

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
