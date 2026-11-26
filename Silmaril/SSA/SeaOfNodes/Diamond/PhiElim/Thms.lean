module

public import Silmaril.SSA.SeaOfNodes.Diamond.PhiElim.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
public import Silmaril.SSA.SeaOfNodes.Pure.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.PhiElim.Correctness

/-! # Exact admission and finite-result preservation -/

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.PhiElim

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs sigs out)

/-- Structural acceptance is exact in the shared typed producer scope. -/
theorem eliminate_eq_some_iff (p : Pure.Program Op inputs out) :
    eliminate g = some p ↔ g.phi.operand .first = g.phi.operand .second ∧
      p = { dataflow := g.dataflow, result := g.phi.operand .first } :=
  Proofs.SSA.SeaOfNodes.Diamond.PhiElim.eliminate_eq_some_iff g p

theorem eliminate_eq_none_iff :
    eliminate g = none ↔ g.phi.operand .first ≠ g.phi.operand .second :=
  Proofs.SSA.SeaOfNodes.Diamond.PhiElim.eliminate_eq_none_iff g

variable (m : Model.{u,v,w} Op) {p : Pure.Program Op inputs out}

/-- Both source results agree in every total pure primitive model. -/
theorem denote_eq (success : eliminate g = some p) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    g.denote m entry = p.eval m entry :=
  Proofs.SSA.SeaOfNodes.Diamond.PhiElim.denote_eq g m success entry

theorem returns_iff (success : eliminate g = some p) (entry : Tuple (Val m.value) (dataPorts inputs))
    (result : sortValue m.value out) :
    g.Returns m entry result ↔ p.eval m entry = result :=
  (g.returns_iff_denote m entry result).trans (by rw [denote_eq g m success entry])

/-- The original γ and the rewritten straight-line graph return the same
singleton tuple in their respective interpretations of the source model. -/
theorem lower_run_eq (success : eliminate g = some p) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    g.lower.run m.toRVSDG entry = p.lower.run (Pure.toRVSDGModel m) entry := by
  rw [p.lower_run]
  exact (g.lower_returns_iff m entry _).mp ((returns_iff g m success entry _).mpr rfl)

end Silmaril.SSA.SeaOfNodes.Diamond.PhiElim
