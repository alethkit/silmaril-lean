module

public import Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.Defs

/-!
# Round 9, REH: the `Step_read` rules that rebind only their state (kernel checks)

* `liftSimpleIdx_fixed`: the `Step_read` rules of the fixed script that pass `liftSimple` are
  exactly `liftSimpleRules` (74 of 103).
* `liftSimpleIs_fixed`: each of them does, read at its index.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec.Sem

set_option maxRecDepth 100000 in
/-- **The rules of `Step_read` that pass `liftSimple`.** -/
theorem liftSimpleIdx_fixed :
    liftSimpleIdx (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) = liftSimpleRules := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Each rule of `liftSimpleRules` passes `liftSimple`.** -/
theorem liftSimpleIs_fixed :
    liftSimpleIs (relsOfDefs Silmaril.Wasm.SpecTec.Scripts.Wasm30.fixed) liftSimpleRules = true := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
