module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Proofs

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (m : Model.{u, v, w} Op) [DecidableEq (sortValue m.value out)]
variable (g : Graph Op inputs sigs out) (entryFacts : Tuple (Fact m.value) (dataPorts inputs))

theorem fold_eq_some_iff (p : Pure.Program Op inputs out) :
    fold m g entryFacts = some p ↔
      ∃ guard : Bool, guardFact m g entryFacts = .constant ⟨guard⟩ ∧ p = select g guard := by
  unfold fold
  cases guardFact m g entryFacts with
  | bottom => simp
  | overdefined => simp
  | constant guard =>
    cases guard with
    | up guard => simp [eq_comm]

theorem fold_eq_none_iff :
    fold m g entryFacts = none ↔
      guardFact m g entryFacts = .bottom ∨ guardFact m g entryFacts = .overdefined := by
  unfold fold
  cases guardFact m g entryFacts <;> simp

theorem executable_eq_singleton {guard : Bool}
    (known : guardFact m g entryFacts = .constant ⟨guard⟩) :
    (SCCP.solve m g entryFacts).1 = {slotIndex (g.phi.merge.slot (Projection.ofBool guard))} := by
  have edges := congrArg Prod.fst (SCCP.solve_fixed m g entryFacts)
  change branchEdges g.phi.merge (guardFact m g entryFacts) = (SCCP.solve m g entryFacts).1 at edges
  rw [known] at edges
  exact edges.symm

theorem denote_eq {p : Pure.Program Op inputs out} (success : fold m g entryFacts = some p)
    {entry : Tuple (Val m.value) (dataPorts inputs)} (covered : TupleCovers entryFacts entry) :
    g.denote m entry = p.eval m entry := by
  obtain ⟨guard, known, rfl⟩ := (fold_eq_some_iff m g entryFacts p).mp success
  have value := SCCP.solve_read_covers m g covered g.predicate
  change (guardFact m g entryFacts).Covers (read m g.predicate entry (g.dataflow.eval m entry PUnit.unit))
    at value
  rw [known] at value
  have agrees := congrArg ULift.down value
  simp only [Graph.denote, Pure.Program.eval, select]
  rw [← agrees]

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP.BranchFold.Proofs
