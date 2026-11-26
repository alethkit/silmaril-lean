module

public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.Defs

/-! # Two pure diamonds connected by a typed join tuple -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs middle results : List (ValueSort Data)}
variable {firstSigs secondSigs : List (List (Ty Data))}

/-- The first join supplies the entire input context for the second diamond.
An original input can remain live by appearing in the first output vector. -/
structure Graph (Op : Signature.{u,v} Data) (inputs middle results : List (ValueSort Data))
    (firstSigs secondSigs : List (List (Ty Data))) where
  first : Arms.Graph Op inputs firstSigs middle
  second : Arms.Graph Op middle secondSigs results

inductive Stage where
  | first
  | second
  deriving DecidableEq

variable (g : Graph Op inputs middle results firstSigs secondSigs) (m : Model.{u,v,w} Op)
variable (entry : Tuple (Val m.value) (dataPorts inputs))

/-- The second source run receives exactly the tuple returned by the first. -/
def Graph.Returns (result : Tuple (Val m.value) (dataPorts results)) : Prop :=
  ∃ joined, g.first.Returns m entry joined ∧ g.second.Returns m joined result

def Graph.denote : Tuple (Val m.value) (dataPorts results) :=
  g.second.denote m (g.first.denote m entry)

end Silmaril.SSA.SeaOfNodes.Diamond.Arms.Sequential
