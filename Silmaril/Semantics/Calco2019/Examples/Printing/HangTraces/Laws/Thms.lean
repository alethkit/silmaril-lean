module

public import Silmaril.Semantics.Calco2019.Examples.Printing.HangTraces.Laws.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingHangTraceLaws

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.HangTraces

variable {A X Y Z : Type u}

theorem iterate_naturality (f : X → Traces A (Y ⊕ X)) (g : Y → Traces A Z) :
    (iterate f >=> g) = iterate (Elgot.mapReturn f g) :=
  LawProofs.naturality f g

theorem iterate_uniformity (f : X → Traces A (Y ⊕ X)) (g : Z → Traces A (Y ⊕ Z))
    (h : X → Z) (comm : (f >=> Elgot.liftPure (Sum.map id h)) = (Elgot.liftPure h >=> g)) :
    iterate f = (Elgot.liftPure h >=> iterate g) :=
  LawProofs.uniformity f g h comm

end Silmaril.Calco2019.Examples.Printing.HangTraces
