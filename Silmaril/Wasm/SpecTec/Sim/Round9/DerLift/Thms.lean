module

public import Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.DerLift.Assemble

/-!
# Round 9, REH: lifting SpecTec derivations backward along export erasure (results)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round9.DerLift`; definitions in `Round9/DerLift/Defs.lean`,
proofs in `Silmaril/Proofs/Wasm/SpecTec/Sim/Round9/DerLift/`.

```lean
theorem dderivesB_lift (hR : ∀ x i, liftRel x = true → RuleLift env O Prov x i) :
    DDerivesB env O x op args v → liftRel x = true → LiftV env O Prov x op args v
theorem eraseBwdAt_of_lift (hb : HostExportBlind host) (P : Profile)
    (hR : ∀ x i, liftRel x = true →
      RuleLift (utf8Env (BI P hn host)) (otherwiseB (utf8Env (BI P hn host))) Prov x i)
    (c : Config H) (hc : Prov "Step" (configV hn c)) : CoreStrip.EraseBwdAt hn P host c
theorem liftSimpleIdx_fixed :
    liftSimpleIdx (relsOfDefs Scripts.Wasm30.fixed) = liftSimpleRules   -- kernel, 74 of 103
theorem ruleLift_simple_BI
    (hZ : ∀ a zv lv, Prov "Step_read" a → a = .case "%;%" (.tuple [zv, lv]) →
      HasTyp (NxPrims.envBI P hn host) VarEnv.empty (.varT "state" []) zv)
    (hi : i ∈ liftSimpleRules) :
    RuleLift (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) Prov "Step_read" i
theorem eraseBwdAt_of_rest (hb : HostExportBlind host)
    (hR : RuleLiftRest (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) Prov)
    (hZ : …) (c : Config H) (hc : Prov "Step" (configV hn c)) : CoreStrip.EraseBwdAt hn P host c
```

`ruleLift_simple_BI` covers 74 of the 103 rules of `Step_read`, `otherwise` rules included (their
`otherwise` by `Round9.ElseLift.otherwiseAtB_lift_read`), at every configuration, collisions of
module instances included: the state is rebound to the original one, not recovered from its
erasure. Not covered: the other 29 rules of `Step_read`, the rules of `Step` and `Step_pure`
(`RuleLiftRest`), and a provenance `Prov` that holds at `configV hn c` and that the remaining rules
keep at their premise inputs.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.dderivesB_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_lift

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.eraseBwdAt_of_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseBwdAt_of_lift

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.liftSimpleIdx_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftSimpleIdx_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.ruleLift_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleLift_simple

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.ruleLift_simple_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ruleLift_simple_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round9.DerLift.eraseBwdAt_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseBwdAt_of_rest

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
