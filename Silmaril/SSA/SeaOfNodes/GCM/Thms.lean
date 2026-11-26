module

public import Silmaril.SSA.SeaOfNodes.GCM.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Legality

public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}

/-- The argument number is checked using the destination signature. The read
site is the end of the source block for that specific branch occurrence. -/
theorem Use.phi_point?_eq_some_iff (source : BlockId Label) (slot : EdgeSlot) (argument : Nat)
    (point : Point Label) :
    (Use.phi source slot argument).point? cfg = some point ↔
      (∃ dst, (shape cfg source).target slot = some dst ∧ argument < dst.1.length) ∧
      point = ⟨source, (shape cfg source).bindings⟩ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.phi_point?_eq_some_iff source slot argument point

/-- The admitted cut follows every supplied operand and makes the result
available at every supplied use, with dominance measured on actual CFG paths. -/
theorem checkPlacement_sound (tree : DominatorTree cfg)
    {operands : List (Point Label)} {uses : List (Use Label)} {candidate : Point Label}
    (checked : checkPlacement tree operands uses candidate = true) :
    Legal cfg operands uses candidate :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.checkPlacement_sound tree checked

end Silmaril.SSA.SeaOfNodes.GCM
