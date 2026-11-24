module

public import Silmaril.RiscV.OperationalInstitution.LPS.Defs

@[expose] public section

namespace Silmaril.RiscV.OperationalInstitution.LPS

open Silmaril.Logic.Operational Silmaril.RiscV.LPS

@[simp] theorem resultOfView_resultView (r : MachineResult (AccessReport MachineState)) :
    resultOfView (resultView r) = some r := by
  cases r <;> rfl

@[simp] theorem encode_eq_iff {a b : Option MachineState} : encode a = encode b ↔ a = b :=
  ⟨congrArg RegisterShape.Config.control, congrArg encode⟩

/-- The model accepts exactly the labelled outcome of the public step. -/
theorem step_iff (segs : List Segment) (s : MachineState) (label : Label) (t : Option MachineState) :
    (system segs).model (encode (some s), label, encode t) ↔
      (label, t) = resultView (stepAccesses segs s) := by
  change (encode (some s) = _ ∧ label = _ ∧ encode t = _) ↔ _
  simp [Prod.ext_iff]

/-- A terminal state has no further RV64 edge. -/
theorem terminal_no_step (segs : List Segment) (label : Label) (dst : shape.Config) :
    ¬ (system segs).model (encode none, label, dst) :=
  id

end Silmaril.RiscV.OperationalInstitution.LPS
