# TLA data denotations

`Silmaril.Logic.Temporal.TLA.DataBridge.Thms` specializes scoped General TLA to
one sort with a caller-supplied Lean carrier `V`. The free scope `scope Rigid
Flex` keeps resolved rigid and flexible names in separate types. A model uses
one rigid valuation for the entire behavior. Each flexible state assigns a
value to every flexible name. The same aliases also work in scopes extended
by General TLA binders. The sort, carrier, and name types share a universe as
required by `General.Scope` and `General.Valuation`. [Bridge definitions](../../Silmaril/Logic/Temporal/TLA/DataBridge/Defs.lean)

The carrier needs no `DecidableEq`, evaluator, or finite enumeration. Callers
can close denotations over their chosen mathematical operations and keep
assumptions about those operations as theorem hypotheses. A model-specific
assumption can be stated as `Admissible : RigidEnv V Γ → Prop` and required of
`M.rigid` when proving a result about a General TLA model `M`. The bridge
uses the model's valuations directly. General TLA's binders and enabledness
use their existing ranges over carrier values and flexible valuations.
[Scoped General TLA](tla.md#scoped-general-tla)

## Handoff from checked selections

After a future elaborator has resolved names and checked expression levels,
it can supply the following denotations over its chosen carrier and scope.

| Selected expression | Denotation and use |
| --- | --- |
| State value or observation | `StateExpr V Γ X` is a `General.Expr`. Use `X = V` for carrier-valued expressions. A Lean observation type in the carrier's universe can go directly into `General.Formula.alwaysBracket`. |
| State proposition | `StatePredicate V Γ` is a proposition-valued state expression. Pass it to `General.StatePred.atom` for a state formula, or to `current` for a source-only action. |
| Raw action | `StepExpr V Γ Prop` is a `General.Action` under one rigid valuation and two ordered flexible states. It can combine `current e` with `prime e` to use the whole expression at the source and target respectively. |

`UNCHANGED` compares the target and source values of the supplied observation
by Lean equality. The bracket admits a raw action step or that same equality,
even when unobserved state changes. `General.Formula.alwaysBracket` uses the
standalone temporal semantics. For fairness at a fixed rigid valuation `ρ`,
the standalone `TLA.Formula.weakFair` and `TLA.Formula.strongFair` take the
raw action and observation specialized at `ρ`. [Checked bridge laws](../../Silmaril/Logic/Temporal/TLA/DataBridge/Thms.lean)

This handoff begins with Lean denotations. A future source elaborator still
needs to establish that its selected denotations interpret the resolved
source expressions and declarations. The existing scalar
`Import.importTemporal` path uses the `Int` and `Bool` signature. It returns
`Elaborator.TemporalFormula`, which lowers with `toFormula signature.noRigid`
and has its own satisfaction equations for bracket and WF/SF. Each path uses
its chosen carrier directly. [Scalar temporal import](https://github.com/hiloopai/silmaril-lean/pull/2986)

## Checked example

A carrier of predicates `Nat → Prop` supplies both values and the observation
in a `General.Formula.alwaysBracket`. The observation intersects the flexible
contents with a rigid set. The formula holds along a behavior where a scratch
coordinate changes while the observed set stays equal and the raw clear
action fails at that step. [Lean example](../../Silmaril/Logic/Temporal/TLA/DataBridge/Examples.lean)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataBridge.Thms \
  +Silmaril.Logic.Temporal.TLA.DataBridge.Examples
make tla-import-check
```
