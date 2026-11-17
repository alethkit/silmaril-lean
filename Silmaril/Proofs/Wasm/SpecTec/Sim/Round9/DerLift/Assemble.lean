module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.DerLift.Simple
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round9.DerLift.Check

/-!
# Round 9, REH: the backward lift, assembled at round 4's primitives

* `ruleLift_simple_BI`: `RuleLift` at the 74 rules of `liftSimpleRules`, at round 4's primitives,
  for every provenance that types the state of a `Step_read` input.
* `eraseBwdAt_of_rest`: `CoreStrip.EraseBwdAt` at an export-blind host from the rule obligations
  left (`RuleLiftRest`) and the provenance of the original image.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (otherwiseB)

/-- `liftSimpleIs_fixed`, read at one rule. -/
theorem liftSimple_at {B : Builtins} {i : Nat} (hi : i ∈ liftSimpleRules) {ps : List Param}
    {op : MixopS} {t : Typ} {rules : List Rule} {r : Rule}
    (hrel : (utf8Env B).findRel? "Step_read" = some (ps, op, t, rules)) (hr : rules[i]? = some r) :
    liftSimple r = true := by
  rw [findRel?_utf8Env] at hrel
  have h := List.all_eq_true.1 liftSimpleIs_fixed _ (EraseAll.mem_rels_of_findRel' hrel)
  simp only [bne_self_eq_false, Bool.false_or, List.all_eq_true] at h
  have h' := h i hi
  rw [hr] at h'
  exact h'

section
variable {H : Type} (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String)
  (host : Silmaril.Wasm.Execution.Core.HostSemantics H)

/-- **`RuleLift` at the 74 `Step_read` rules of `liftSimpleRules`**, at round 4's primitives,
for every provenance that types the state of a `Step_read` input. -/
theorem ruleLift_simple_BI {Prov : IL.Id → Value → Prop}
    (hZ : ∀ a zv lv, Prov "Step_read" a → a = .case "%;%" (.tuple [zv, lv]) →
      HasTyp (NxPrims.envBI P hn host) VarEnv.empty (.varT "state" []) zv)
    {i : Nat} (hi : i ∈ liftSimpleRules) :
    RuleLift (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) Prov "Step_read" i :=
  ruleLift_simple (NxPrims.builtinsVT_BI P hn host) (NxClause.biErase_QT_BI P hn host)
    (ElseRef.elseBwdB_BI P hn host) hZ fun _ _ _ _ _ hrel hr => liftSimple_at hi hrel hr

/-- **The backward SpecTec leaf from the rule obligations left**, at an export-blind host: given
`RuleLiftRest` (every rule of `Step` and `Step_pure`, and the 29 rules of `Step_read` outside
`liftSimpleRules`), a provenance that types the state of a `Step_read` input, and the provenance
of `configV hn c`. -/
theorem eraseBwdAt_of_rest (hb : HostExportBlind host) {Prov : IL.Id → Value → Prop}
    (hR : RuleLiftRest (NxPrims.envBI P hn host) (otherwiseB (NxPrims.envBI P hn host)) Prov)
    (hZ : ∀ a zv lv, Prov "Step_read" a → a = .case "%;%" (.tuple [zv, lv]) →
      HasTyp (NxPrims.envBI P hn host) VarEnv.empty (.varT "state" []) zv)
    (c : Silmaril.Wasm.Execution.Core.Config H) (hc : Prov "Step" (configV hn c)) :
    CoreStrip.EraseBwdAt hn P host c := by
  refine eraseBwdAt_of_lift hb P (fun x i hx => ?_) c hc
  by_cases hs : x = "Step_read" ∧ i ∈ liftSimpleRules
  · obtain ⟨rfl, hi⟩ := hs
    exact ruleLift_simple_BI P hn host hZ hi
  · exact hR x i hx hs

end

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
