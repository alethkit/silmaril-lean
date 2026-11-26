module

public import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Defs

/-! Pointwise comparison and wire lookup for the shared abstract producer table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP

open RVSDG (Port Tuple Locals Origin)

variable {Data : Type*} {value : Data → Type*}
variable {args : List (Ty Data)} {past : List (List (Ty Data))}

def TupleLE (lhs rhs : Tuple (Fact value) args) : Prop :=
  ∀ {t} (port : Port args t), lhs.get port ≤ rhs.get port

def LocalsLE (lhs rhs : Locals (Fact value) past) : Prop :=
  ∀ i, TupleLE (lhs.get i) (rhs.get i)

/-- Read a typed origin from an abstract local store, as in the native evaluator. -/
def readLocal (argsFacts : Tuple (Fact value) args) (locals : Locals (Fact value) past)
    {t : Ty Data} : Origin args past t → Fact value t
  | .arg port => argsFacts.get port
  | .output i port => (locals.get i).get port

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP
