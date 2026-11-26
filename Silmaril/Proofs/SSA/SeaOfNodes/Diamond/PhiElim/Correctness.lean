module

public import Silmaril.SSA.SeaOfNodes.Diamond.PhiElim.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.PhiElim

open Silmaril.SSA.SeaOfNodes
open Diamond Diamond.PhiElim
open Silmaril.SSA.RVSDG (Origin Tuple Wires)

universe u v w

private theorem origin_address_iff {T : Type u} {args : List T} {past : List (List T)} {t : T}
    (left right : Origin args past t) : left.address = right.address ↔ left = right := by
  constructor
  · intro same
    have sameWire : (.cons left .nil : Wires args past [t]) = .cons right .nil :=
      Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective _ _
        (by simp only [Wires.addresses, same])
    exact congrArg (fun wires => wires.get .head) sameWire
  · exact congrArg Origin.address

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs sigs out) (m : Model.{u,v,w} Op)

theorem eliminate_eq_some_iff (p : Pure.Program Op inputs out) :
    eliminate g = some p ↔ g.phi.operand .first = g.phi.operand .second ∧
      p = { dataflow := g.dataflow, result := g.phi.operand .first } := by
  constructor
  · intro success
    by_cases same : (g.phi.operand .first).address = (g.phi.operand .second).address
    · rw [eliminate, ite_eq_left same] at success
      exact ⟨(origin_address_iff _ _).mp same, (Option.some.inj success).symm⟩
    · simp [eliminate, same] at success
  · rintro ⟨same, rfl⟩
    simp [eliminate, same]

theorem eliminate_eq_none_iff :
    eliminate g = none ↔ g.phi.operand .first ≠ g.phi.operand .second := by
  have addressIff := origin_address_iff (g.phi.operand .first) (g.phi.operand .second)
  by_cases same : (g.phi.operand .first).address = (g.phi.operand .second).address <;>
    simp [eliminate, same, ← addressIff]

theorem denote_eq {p : Pure.Program Op inputs out} (success : eliminate g = some p)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : g.denote m entry = p.eval m entry := by
  obtain ⟨same, rfl⟩ := (eliminate_eq_some_iff g p).mp success
  simp only [Graph.denote, Pure.Program.eval]
  cases g.phi.merge.slot (Projection.ofBool
    (read m g.predicate entry (g.dataflow.eval m entry PUnit.unit)).down) with
  | first => rfl
  | second => rw [same]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.PhiElim
