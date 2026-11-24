module

public import Silmaril.Logic.Arithmetic.Buchi.Thms
public import Silmaril.LogicGraph.Nodes.Logic.Arithmetic.Defs

silmaril comorphism logic.arithmetic.presburger_to_buchi := Silmaril.Logic.Arithmetic.Buchi.presburgerToBuchi
  (title := "Presburger inclusion into Büchi arithmetic")
  (facts := [Silmaril.Logic.Arithmetic.Buchi.presburgerToBuchi_modelExpansive])
