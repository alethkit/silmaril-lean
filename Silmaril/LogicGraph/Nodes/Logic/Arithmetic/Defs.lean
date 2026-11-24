module

public import Silmaril.Logic.Arithmetic.Buchi.Defs
public import Silmaril.Project.Registry.Institution.Defs

silmaril institution logic.arithmetic.presburger := Silmaril.Logic.Arithmetic.Buchi.presburger
  (title := "Presburger arithmetic")

silmaril institution logic.arithmetic.buchi := Silmaril.Logic.Arithmetic.Buchi.buchi
  (title := "Büchi arithmetic (base 2)")
