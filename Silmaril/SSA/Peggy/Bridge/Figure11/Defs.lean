module

public import Silmaril.SSA.PEG.Semantics.Defs
public import Silmaril.SSA.Peggy.Acyclic.Defs

/-! # Common interpretations for loop-free Peggy and Figure 11 -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Figure11

open RVSDG (Tuple)
open Acyclic (Ranked)

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {n : Nat}

/-- Figure 11 uses lifted Bool and Nat. Data carriers are retained verbatim. -/
def valueEquiv (carrier : Data → Type) :
    (t : PEG.Ty Data) → Acyclic.Value carrier t ≃ PEG.Ty.Value carrier t
  | .bool => Equiv.ulift.symm
  | .count => Equiv.ulift.symm
  | .data _ => Equiv.refl _

def toAcyclic (m : PEG.Interpretation.{0,0,0} P) : Acyclic.Interpretation P where
  carrier := m.carrier
  prim instr args :=
    (m.run instr (args.map fun t => valueEquiv m.carrier t)).map
      (valueEquiv m.carrier _).symm

/-- Figure 11 takes defined tuple inputs. The bridge injects them at exactly
the same parameter positions into its partial input environment. -/
def toInputs (m : PEG.Interpretation.{0,0,0} P) (env : Tuple m.Value params) :
    (toAcyclic m).Inputs params :=
  fun i => some ((valueEquiv m.carrier params[i]).symm (env.get (PEG.portAt params i)))

def liftPartial (m : PEG.Interpretation.{0,0,0} P) {t : PEG.Ty Data}
    (value : (toAcyclic m).Partial t) : Option (m.Value t) :=
  value.map (valueEquiv m.carrier t)

/-- The nodewise bridge valuation is constant in the empty loop frame. -/
def valuation {g : PEG.Graph P params results n 0} (r : Ranked g)
    (m : PEG.Interpretation.{0,0,0} P) (env : Tuple m.Value params) : g.Valuation m :=
  fun q => liftPartial m (r.eval (toAcyclic m) (toInputs m env) q.1)

end Silmaril.SSA.Peggy.Bridge.Figure11
