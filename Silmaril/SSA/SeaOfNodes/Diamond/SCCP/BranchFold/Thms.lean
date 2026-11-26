module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Correctness

/-! Exact admission and source-native return correspondence for branch folding. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
variable (g : Graph Op inputs sigs out) (entryFacts : Tuple (Fact m.value) (dataPorts inputs))

/-- Acceptance selects the wire from the Region slot for the constant guard. -/
theorem fold_eq_some_iff (p : Pure.Program Op inputs out) :
    fold m g entryFacts = some p ↔
      ∃ guard : Bool, guardFact m g entryFacts = .constant ⟨guard⟩ ∧ p = select g guard :=
  Proofs.fold_eq_some_iff m g entryFacts p

theorem fold_eq_none_iff :
    fold m g entryFacts = none ↔
      guardFact m g entryFacts = .bottom ∨ guardFact m g entryFacts = .overdefined :=
  Proofs.fold_eq_none_iff m g entryFacts

/-- The fixed-point executable set contains just the selected occurrence. -/
theorem executable_eq_singleton {guard : Bool}
    (known : guardFact m g entryFacts = .constant ⟨guard⟩) :
    (SCCP.solve m g entryFacts).1 = {slotIndex (g.phi.merge.slot (Projection.ofBool guard))} :=
  Proofs.executable_eq_singleton m g entryFacts known

variable {entryFacts} {p : Pure.Program Op inputs out} {entry : Tuple (Val m.value) (dataPorts inputs)}

/-- Every concrete entry covered by the analysis returns the value of the
wire selected by the rewrite. -/
theorem denote_eq (success : fold m g entryFacts = some p) (covered : TupleCovers entryFacts entry) :
    g.denote m entry = p.eval m entry :=
  Proofs.denote_eq m g entryFacts success covered

theorem returns_iff (success : fold m g entryFacts = some p) (covered : TupleCovers entryFacts entry)
    (result : sortValue m.value out) :
    g.Returns m entry result ↔ p.eval m entry = result :=
  (g.returns_iff_denote m entry result).trans (by rw [denote_eq m g success covered])

/-- The existing γ lowering and the regionless lowering of the rewrite
return the same singleton tuple at each covered entry. -/
theorem lower_run_eq (success : fold m g entryFacts = some p) (covered : TupleCovers entryFacts entry) :
    g.lower.run m.toRVSDG entry = p.lower.run (Pure.toRVSDGModel m) entry := by
  rw [p.lower_run]
  exact (g.lower_returns_iff m entry _).mp ((returns_iff m g success covered _).mpr rfl)

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold
