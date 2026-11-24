module

public import Silmaril.Logic.Operational.Machines.Thms
public import Silmaril.RiscV.LPS.Machine

/-!
# LPS RV64 operational transitions

For a fixed loaded segment list, use `stepAccesses` as the transition source.
Expose the integer register reads and the overlay-first byte view. The control
carrier keeps the complete state and provides a terminal configuration for
fault and unmodeled outcomes. Step labels keep the distinction and the exact
access report on success.
-/

@[expose] public section

namespace Silmaril.RiscV.OperationalInstitution.LPS

open Silmaril.Logic.Operational Silmaril.RiscV.LPS

/-- The LPS machine result, with the reported data-access ranges on success. -/
inductive Label where
  | advance (ranges : List MemoryAccess)
  | fault
  | unmodeled
  deriving DecidableEq

def shape : RegisterShape :=
  ⟨Option MachineState, Reg, Word, Word, Byte, Label⟩

/-- Canonical integer register and byte observations of the complete state. -/
def encode (state : Option MachineState) : shape.Config :=
  ⟨state, state.elim (fun _ => (0 : Word)) MachineState.reg,
    state.elim (fun _ => none) MachineState.readByte⟩

/-- Encode the existing result as a label and optional successor state. -/
def resultView : MachineResult (AccessReport MachineState) → Label × Option MachineState
  | .ok report => (.advance report.ranges, some report.value)
  | .fault => (.fault, none)
  | .unmodeled => (.unmodeled, none)

/-- Recover results from the canonical label/target pairs. -/
def resultOfView : Label × Option MachineState → Option (MachineResult (AccessReport MachineState))
  | (.advance ranges, some state) => some (.ok ⟨state, ranges⟩)
  | (.fault, none) => some .fault
  | (.unmodeled, none) => some .unmodeled
  | _ => none

/-- One edge of the LPS step interface. The state projections are canonical
and a terminal configuration has no outgoing edge. -/
def model (segs : List Segment) : (RegisterShape.signatures.obj shape).Model
  | (src, label, dst) =>
    match src.control with
    | none => False
    | some s =>
      let view := resultView (stepAccesses segs s)
      src = encode (some s) ∧ label = view.1 ∧ dst = encode view.2

def system (segs : List Segment) : RegisterSystem :=
  ⟨shape, model segs⟩

end Silmaril.RiscV.OperationalInstitution.LPS
