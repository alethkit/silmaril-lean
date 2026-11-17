module

public import Silmaril.Wasm.SpecTec.Sim.Round9.ElseLift.Defs
public import Silmaril.Wasm.SpecTec.Sim.Round9.CoreStrip.Defs

/-!
# Round 9, REH: lifting SpecTec derivations backward along export erasure (definitions)

`CoreStrip.EraseBwdAt` (the backward SpecTec leaf of REH) asks for a derivation of `Step` at
`configV hn c` whose erasure is a given derivation's conclusion at the erased image. Route 2 of
rounds 7 to 9 moves derivations only *forward* along `Swap.eraseV`, outside `otherwise`
(`Round8.NxDer.derFwdN`, `Round9.ElseRef.sStepB_fwd_BI_E`). Forward is easy because erasure is a
function: every quantifier value is erased. Backward is not: erasure forgets export lists, and
two module instances of `c` may differ only in them (`Round7.REGap.collideCfg`), so the
export-carrying quantifiers of a rule instance must be **rebound positionally**, to the values at
their positions in the original input, not chosen by their erased value.

This header states the interface of that lift, with the provenance of the original input explicit:

* `liftRel x`: the relations lifted by induction, `Step`, `Step_read` and `Step_pure`. The others
  (`Ref_ok`, `Expand`, …) appear only as premises and are handled at the rule.
* `LiftV env O Prov x op args v₀`: **the lift at one erased conclusion**. For every original input
  `a` with `v₀ = (eraseV a, b₀)` whose provenance `Prov x a` holds, rule-based derivations of `x`
  reach `(a, b)` for some `b` with `eraseV b = b₀`. The successor is exact: no Core round trip,
  and the `CALL_REF` annotations and nondeterministic choices of `b` are those of the derivation.
* `DPremL env O Prov els ρ pr`: `Round6.Reading.DPremB` whose relation premises of `liftRel`
  relations also carry `LiftV` at their conclusion: the induction hypothesis, at the premises.
* `RuleLift env O Prov x i`: **the obligation at rule `i` of `x`**: a rule instance on the erased
  side (quantifiers typed, conclusion evaluated, premises with their lifts) gives `LiftV` at its
  conclusion. A proof rebinds the export-carrying quantifiers to positions of `a`, shows the
  premise inputs keep `Prov`, and reads `otherwise` by `Round9.ElseLift.otherwiseAtB_lift`.

`Round9.DerLift.dderivesB_lift` proves `LiftV` from `RuleLift` at every rule, by induction on the
erased derivation; `eraseBwdAt_of_lift` gives `CoreStrip.EraseBwdAt` from it at an export-blind
host, given `Prov "Step" (configV hn c)`. `Round9.DerLift.ruleLift_simple` proves `RuleLift` at
the `Step_read` rules of the family `liftSimple`, for any `Prov` that types the state.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round9.DerLift

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.SpecTec.Sim.Round7
open Round6.Reading (DDerivesB DPremB conclAlts)

/-- The relations lifted by induction: `Step`, `Step_read`, `Step_pure`. -/
def liftRel (x : IL.Id) : Bool := x == "Step" || x == "Step_read" || x == "Step_pure"

/-- **The backward lift at one erased conclusion `v₀`** of `x`: every original input `a` with
provenance `Prov x a` and `v₀ = (eraseV a, b₀)` has a derivation of `(a, b)` with
`eraseV b = b₀`. -/
def LiftV (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) (x : IL.Id) (op : MixopS)
    (args : List ArgV) (v₀ : Value) : Prop :=
  ∀ a b₀, v₀ = .tuple [Swap.eraseV a, b₀] → Prov x a →
    ∃ b, DDerivesB env O x op args (.tuple [a, b]) ∧ Swap.eraseV b = b₀

/-- **`DPremB` with the lift at its `liftRel` relation premises.** -/
inductive DPremL (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) :
    Prop → VarEnv → Prem → Prop where
  | ifPr {els : Prop} {ρ : VarEnv} {e : Exp} :
      EvalExp env ρ e (.bool true) → DPremL env O Prov els ρ (.ifPr e)
  | elsePr {els : Prop} {ρ : VarEnv} : els → DPremL env O Prov els ρ .elsePr
  | letPr {els : Prop} {ρ : VarEnv} {e₁ e₂ : Exp} {w : Value} :
      EvalExp env ρ e₂ w → EvalExp env ρ e₁ w → DPremL env O Prov els ρ (.letPr e₁ e₂)
  | rulePr {els : Prop} {ρ : VarEnv} {x : IL.Id} {args : List Arg} {op : MixopS} {e : Exp}
      {avs : List ArgV} {w : Value} :
      EvalArgs env ρ args avs → EvalExp env ρ e w → DDerivesB env O x op avs w →
      (liftRel x = true → LiftV env O Prov x op avs w) →
      DPremL env O Prov els ρ (.rulePr x args op e)
  | iterOptNone {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → (∀ p ∈ xvs, p.2 = .opt none) →
      DPremL env O Prov els ρ (.iterPr pr (.mk .opt ds))
  | iterOptSome {els : Prop} {ρ : VarEnv} {pr : Prem} {ds : List Dom}
      {xvs row : List (IL.Id × Value)} :
      EvalDoms env ρ ds xvs → ds ≠ [] → domSomes xvs = some row →
      DPremL env O Prov els (ρ.bindVals row) pr →
      DPremL env O Prov els ρ (.iterPr pr (.mk .opt ds))
  | iterList {els : Prop} {ρ : VarEnv} {pr : Prem} {it : Iter} {ds : List Dom}
      {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)} {k : Nat} :
      (it = .list ∨ (it = .list1 ∧ 1 ≤ k)) →
      EvalDoms env ρ ds xvs → ds ≠ [] → domLists xvs = some dls →
      (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls none k, DPremL env O Prov els (ρ.bindVals r) pr) →
      DPremL env O Prov els ρ (.iterPr pr (.mk it ds))
  | iterListN {els : Prop} {ρ : VarEnv} {pr : Prem} {eₙ : Exp} {ido : Option IL.Id}
      {ds : List Dom} {xvs : List (IL.Id × Value)} {dls : List (IL.Id × List Value)}
      {kv : Value} {k : Nat} :
      EvalDoms env ρ ds xvs → EvalExp env ρ eₙ kv → kv.asNat? = some k →
      domLists xvs = some dls → (∀ d ∈ dls, d.2.length = k) →
      (∀ r ∈ iterRows dls ido k, DPremL env O Prov els (ρ.bindVals r) pr) →
      DPremL env O Prov els ρ (.iterPr pr (.mk (.listN eₙ ido) ds))

/-- **The obligation at rule `i` of `x`**: an instance of the rule on the erased side, with the
lift at its `liftRel` premises, has the lift at its conclusion. -/
def RuleLift (env : Env) (O : ElseI) (Prov : IL.Id → Value → Prop) (x : IL.Id) (i : Nat) :
    Prop :=
  ∀ {op : MixopS} {args : List ArgV} {v₀ : Value} {ps : List Param} {t : Typ}
    {rules : List Rule} {nm : IL.Id} {qs : List Param} {e e' : Exp} {prems : List Prem}
    {ρ₀ : VarEnv} {σ : List (IL.Id × Value)},
    env.findRel? x = some (ps, op, t, rules) → rules[i]? = some (.ruleD nm qs op e prems) →
    e' ∈ conclAlts e → bindParams VarEnv.empty ps args = some ρ₀ →
    QuantsOk env (ρ₀.bindVals σ) qs → EvalExp env (ρ₀.bindVals σ) e' v₀ →
    (∀ pr ∈ prems, DPremL env O Prov (O x args i v₀) (ρ₀.bindVals σ) pr) →
    LiftV env O Prov x op args v₀

end Silmaril.Wasm.SpecTec.Sim.Round9.DerLift
