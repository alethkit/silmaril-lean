module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms

open Silmaril.SSA
open SeaOfNodes.Diamond SeaOfNodes.Diamond.Arms
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs results : List (ValueSort Data)} {sigs : List (List (Ty Data))}

theorem returns_iff_denote (m : Model.{u,v,w} Op) (g : Graph Op inputs sigs results)
    (entry : Tuple (Val m.value) (dataPorts inputs)) (result : Tuple (Val m.value) (dataPorts results)) :
    g.Returns m entry result ↔ g.denote m entry = result := by
  have taken {b : Bool} {p : Projection} (h : Projection.Taken b p) : Projection.ofBool b = p := by
    cases h <;> rfl
  constructor
  · rintro ⟨branch, arrival⟩
    dsimp only [Arms.Graph.denote]
    rw [taken branch, ← arrival, Merge.slot_predecessor]
  · rintro rfl
    cases readBit : (read m g.predicate entry (g.shared.eval m entry PUnit.unit)).down with
    | false =>
      simpa only [Arms.Graph.denote, readBit, Projection.ofBool] using
        (Arms.Graph.Returns.ret (g := g) (m := m) (entry := entry)
          (readBit.symm ▸ Projection.Taken.onFalse) (g.merge.predecessor_slot .onFalse))
    | true =>
      simpa only [Arms.Graph.denote, readBit, Projection.ofBool] using
        (Arms.Graph.Returns.ret (g := g) (m := m) (entry := entry)
          (readBit.symm ▸ Projection.Taken.onTrue) (g.merge.predecessor_slot .onTrue))

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.Arms
