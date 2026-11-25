module

public import Silmaril.SSA.MLIR.Institution.Arith.Defs
public import Silmaril.SSA.MLIR.Arith.Examples.Defs

@[expose] public section

namespace Silmaril.MLIR.Institution.Arith.Examples

open CategoryTheory
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.Arith.Examples (i1 i8)

/-- An arithmetic dialect whose sorts and operation symbols carry an extra tag. -/
def taggedSignature : Signature true where
  Ty := Width × Bool
  Op p := Op (p.map Prod.fst) × Bool

/-- Add the tag throughout the typed profile, including the isolated region interface. -/
def tag : signature ⟶ taggedSignature where
  sort w := (w, true)
  symbol o := (o, true)

def taggedModel : Model taggedSignature where
  carrier w := model.carrier w.1
  op o := model.op o.1

def squareInput : Env [i1, i8] := .cons 1#1 (.cons 20#8 .nil)

end Silmaril.MLIR.Institution.Arith.Examples
