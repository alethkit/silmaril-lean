module

public import Silmaril.SSA.Peggy.EPEG.Defs

/-! # Structural evidence for the node equations of a PEG selection -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Selection

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : PEG.InstructionSet.{u,v} Data}
variable {params results : List (PEG.Ty Data)} {n n' l : Nat}
variable {source : PEG.Graph P params results n l} {target : PEG.Graph P params results n' l}

/-- Bind an actual candidate row and its chosen source representative's row
to the same label and ordered profile, retaining both typed operand lists. -/
structure Row (sel : Selection source target) (vertex : Fin n') where
  inputs : List (PEG.Ty Data)
  label : PEG.Label P params (Fin l) inputs (target.sort vertex)
  sourceArgs : Tuple (PEG.Ref source.sort) inputs
  targetArgs : Tuple (PEG.Ref target.sort) inputs
  sourceNode : HEq (source.node (sel.representative vertex).id)
    (PEG.Node.ofLabel label sourceArgs)
  targetNode : target.node vertex = PEG.Node.ofLabel label targetArgs

/-- For every ordered operand, check that the candidate's selected child
belongs to the class used by the chosen source row. -/
def Row.check {sel : Selection source target} {vertex : Fin n'} (row : Row sel vertex)
    (classes : Classes n) : Bool :=
  (List.finRange row.inputs.length).all fun i =>
    let port := PEG.portAt row.inputs i
    classes (row.sourceArgs.get port).id == classes (sel.sourceRef (row.targetArgs.get port)).id

def checkRows {sel : Selection source target} (rows : ∀ vertex, Row sel vertex)
    (classes : Classes n) : Bool :=
  (List.finRange n').all fun vertex => (rows vertex).check classes

end Silmaril.SSA.Peggy.EPEG.Selection
