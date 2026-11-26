module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Defs

/-! # Lower a checked ordered PEG loop to the existing λSSA loop form -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA

open RVSDG (Port Tuple)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG.LambdaSSA.Theta

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}

abbrev Packet (carried : List (Ty Data)) := Operational.Packed (valuePorts carried)

/-- Lower through the already checked numbered RVSDG compiler. -/
def lower (b : Bundle g slot allowInvariant) :
    Isotope.LambdaSSA.Region (Operational.Instruction (Region.Opcode P) (valuePorts carried)) :=
  Operational.lower b.compile

def runFuel (b : Bundle g slot allowInvariant) (m : TotalModel P)
    (fuel : Nat) (input : Tuple m.toPEG.Value carried) : Option (Tuple m.toPEG.Value carried) :=
  (Operational.runFuel (Region.model m) b.compile fuel (encode m input)).map
    (fromPorts (F := (Region.model m).Val) carried)

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA
