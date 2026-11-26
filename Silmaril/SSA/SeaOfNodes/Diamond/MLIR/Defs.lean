module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs
public import Silmaril.SSA.RVSDG.MLIR.Graph.Defs

/-! # A pure Sea of Nodes diamond in scoped MLIR

The existing diamond lowering supplies the numbered RVSDG graph. The scoped
MLIR dialect interprets its dispatch as a total primitive and its γ as the
application of one selected isolated body to the captured operands.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR

open RVSDG (Tuple)
open Silmaril.MLIR.Institution (Block Equation)

variable {Data : Type} {Op : Diamond.Signature.{0, 0} Data}
variable {inputs : List (ValueSort Data)} {sigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}

/-- The diamond's existing opcode family over the scoped dialect's empty state alphabet. -/
abbrev source (Op : Diamond.Signature.{0, 0} Data) : RVSDG.MLIR.Graph.Source (ValueSort Data) :=
  ⟨Opcode Op⟩

/-- Interpret the scoped dialect using the diamond's value carriers and total primitives. -/
abbrev model (m : Model.{0, 0, 0} Op) :
    Silmaril.MLIR.Institution.Model (RVSDG.MLIR.Graph.signature (source Op)) :=
  RVSDG.MLIR.Graph.model (P := source Op) m.toRVSDG

/-- Lower the diamond using the typed RVSDG graph and scoped MLIR block interfaces. -/
def lower (g : Graph Op inputs sigs out) :
    Block (RVSDG.MLIR.Graph.signature (source Op))
      (dataPorts inputs).get (dataPorts [out]).get :=
  RVSDG.MLIR.Graph.lower (P := source Op) g.lower

/-- Read the lowered block's sole returned value at the corresponding input assignment. -/
def denote (m : Model.{0, 0, 0} Op) (g : Graph Op inputs sigs out)
    (entry : Tuple (Val m.value) (dataPorts inputs)) : sortValue m.value out :=
  (lower g (0 : Fin 1)).denote (model m) (RVSDG.MLIR.Graph.toAssignment entry)

/-- Compare the lowered blocks of two diamonds with the same entry and result types. -/
def lowerEquation {rightSigs : List (List (Diamond.Ty Data))}
    (lhs : Graph Op inputs sigs out) (rhs : Graph Op inputs rightSigs out) :
    Equation (RVSDG.MLIR.Graph.signature (source Op)) where
  inputs := (dataPorts inputs).length
  outputs := 1
  context := (dataPorts inputs).get
  results := (dataPorts [out]).get
  lhs := lower lhs
  rhs := lower rhs

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR
