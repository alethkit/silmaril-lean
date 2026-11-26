module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.Semantics.Elgot.Defs

/-! # Partial denotation of a pure single loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}

/-- Iterate the total header step from the entry latch tuple. Membership
observes only finite returns. -/
noncomputable def Graph.denote (g : Graph Op inputs carried entrySigs headerSigs out)
    (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) (dataPorts inputs)) :
    Part (sortValue m.value out) :=
  let iterate := Silmaril.Elgot.Part.run
    (fun old => Part.some ((g.step m input old).map (ULift.up.{u}) id)) (g.initial m input)
  iterate.map ULift.down

end Silmaril.SSA.SeaOfNodes.Loop
