# Named TLA+ temporal denotations over mathematical data

Import `Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms`. Resolve the
parsed module registry with `Resolution.resolveWith .levelSyntax`, then
select a nullary source definition by its resolved `BindingId` with
`Temporal.lowerFormula registry externalLevels signature maxDepth id`.
`lowerState` and `lowerAction` select a state predicate or a two-endpoint
relation. Each entry checks levels on the supplied registry before lowering.
A constant or state predicate is also a formula. A raw action is rejected
in a formula position.
[Entry points](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Defs.lean) ·
[Level checking](tla-expression-levels.md)

Supply an `Interpretation` with DataElab operations, Boolean policy and
admitted primitive interpretations. The pure-set and tagged adapters both
fit this interface. For example, use
`⟨policy.operations, policy.booleans, policy.external table⟩` with the tagged
numeric signature. Then use `checked.toFormula interpretation rigid` for a
standalone Simple TLA formula. The rigid valuation is fixed throughout
satisfaction. Each state is a total map from flexible declaration IDs to
values in the chosen carrier. A primed data operand uses the target map
and the same rigid valuation.
[Denotations](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Semantics.lean) ·
[DataElab adapters](tla-data-elab.md) · [Standalone semantics](tla.md#typed-simple-tla)

| Form | Lowering |
| --- | --- |
| State and step predicates | Core DataElab expressions, with prime in step positions. Negation, the four binary Boolean operators, and junction lists compose predicates, including modal predicates, using the data Boolean policy. |
| Observations | A core DataElab state expression or an inline flat tuple of such expressions. The evaluator compares their values position by position at the two endpoints. It rejects a retained prime even when a primitive level signature masks that operand's contribution. |
| `UNCHANGED e`, `[A]_e`, `<<A>>_e` | Observation equality, disjunction with equality, and conjunction with inequality, respectively. A square step can change coordinates outside its observation. |
| `ENABLED A` | Exists a successor flexible valuation satisfying the action at the current state. The witness ranges over the whole carrier at each coordinate. It is independent of any next state in a behavior. |
| Temporal Boolean composition | Negation, conjunction, disjunction, implication, equivalence and junction lists. State children contribute their truth at the current instant. |
| `[]F`, `<>F`, `F ~> G` | Standalone always, eventually and leads-to. The matching action forms are `[][A]_e` and `<><<A>>_e`. |
| `WF_e(A)` and `SF_e(A)` | Standalone weak and strong fairness of the changing steps of `A` under observation `e`. Fairness uses the same full successor space as ENABLED. |

The resulting formulas inherit Simple TLA's checked whole-state stutter
invariance. Source raw actions remain relations on two endpoints. Data
predicates use the fixed interpretation's truth test and malformed-Boolean
policy. Once composition reaches temporal level, its Boolean connectives
combine propositions about behaviors.
[Action and stuttering laws](../../Silmaril/Logic/Temporal/TLA/DataElab/Temporal/Thms.lean) ·
[Lamport, *Specifying Systems*, §16.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=330)

The temporal syntax expands nullary module operators at their original
resolved sites, including operators reached through EXTENDS. Core DataElab
leaves retain their ordinary first-order calls, LET expansion and data
binders. Lifting modal forms through parameterized calls, LET, quantifiers,
value constructors or IF is a further slice. Other boundaries include
INSTANCE replay, collection-profile leaves, value-level tuple constructors,
temporal primitives, action composition, guarantees, and checking source
proofs. This is a mathematical semantics with a source admission check.
There is no general source adequacy or finite model-checking claim.

## Intact LiveHourClock

The fixture uses the pinned parser revision and checks all four downloaded
source hashes before parsing.

| Source at `bc1b506bdcad80bb518bf3776a9161c34ff0fc4c` | SHA-256 |
| --- | --- |
| [LiveHourClock.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/LiveHourClock.tla) | `d363d32fa6a20f7aa6b2590ba95e2a4ffd7849107423ae3bbc5ac96d10693064` |
| [HourClock.tla and Naturals.tla](tla-source-acceptance.md#inputs-and-library-contract) | Existing source acceptance pins |
| [TLCExt.tla](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules/TLCExt.tla) | `6c3e7e54cf1b8a4d2d1c7a5fd088f06452edce68ec28d8be99392cc0037a5399` |

The registry parses the intact LiveHourClock and HourClock modules and
attests the two needed Naturals infix declarations from the parsed standard
module. TLC contributes an empty signature to this fixture. The parsed
TLCExt module attests a nullary `CounterExample` used to resolve and
level-check the original postcondition. The fixture does not admit a TLC
counterexample interpretation.

Lean checks that satisfaction of the lowered `LSpec` implies satisfaction
of `AlwaysTick` and `TypeInvariance` over arbitrary tagged valuations
and a fixed tagged adapter policy. The proof preserves the range 1 through
12 across both raw clock updates and idle steps. From every in-range state
it constructs a changing successor and uses weak fairness to obtain a tick
at or after each instant. `AllTimes` and `ClockSettles` are rejected at
their temporal quantifiers. Selecting `PostCondition` reports the missing
`CounterExample` interpretation. The original anonymous theorem contains
`AllTimes`, so the checked progress and invariant result covers two of its
three conjuncts.
[Fixture proof and admission checks](../../tests/semantics/tla-temporal-source/LiveHourClock.lean)

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Examples
python3 -I tests/semantics/tla-temporal-source/check.py
make tla-import-check
```
