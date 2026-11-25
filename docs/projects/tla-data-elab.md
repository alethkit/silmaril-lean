# TLA+ data expression lowering

Import `Silmaril.Logic.Temporal.TLA.DataElab.Defs`. Parse with
`Surface.Parser.parseModule`, resolve a registry with `Resolution.resolve`,
then call `DataElab.lowerDefinition registry signature maxDepth id` on a
resolved, nullary source operator. Resolve the operator's declaration ID
through the root's final scope when selecting an entry by name. Use
`checked.eval ops booleans external valuation` for its value in one
state. Use `booleans.holds` on that value when a caller needs a proposition.

[Lowering API](../../Silmaril/Logic/Temporal/TLA/DataElab/Defs.lean) ·
[Denotation](../../Silmaril/Logic/Temporal/TLA/DataElab/Semantics.lean) ·
[Module resolution](tla-module-resolution.md) · [Mathematical data model](tla-data.md)

## Scope and substitution

- The lowering reads each use from the resolver at its original module and
  path. An imported operator expands in its home module, where it can still
  refer to LOCAL definitions. LET definitions capture the incoming lexical
  bindings, including earlier LET definitions and enclosing formals.
- Expression actuals substitute expanded terms. Named and symbolic operator
  actuals retain their resolved identity or lexical closure. A lambda keeps
  its own body site and captures the actual's lexical context. Operator
  formals can be forwarded through another invocation.
- Rigid constants and flexible variables have separate assignments keyed by
  declaration identity. A caller evaluating across states fixes the rigid
  assignment and varies the flexible one. Each expansion of a binder gets a
  fresh witness slot. The result carries a check that witnesses are scoped and
  that each external node has the admitted arity.
- The depth bound starts at the selected body and counts descent through the
  source, including expansion into called bodies. `expansionLimit` gives the
  next unvisited site. The resolver checks names and arities even in unused
  bodies. Lowering checks the requested expression and the bodies it expands,
  including expression actuals even when unused. An uncalled LET operator
  or unapplied operator actual does not require a data denotation.

The public interfaces leave a place for a compositional level check to consume
the same resolved registry and declaration paths before evaluation.
`primeRequiresLevels` identifies a resolved prime use at its source site,
including one reached through a call. Future prime semantics need to evaluate
the *whole substituted operand* with a shifted flexible valuation and the same
rigid bindings. For example, expanding `P(e) == e'` requires the flexible
reads of the actual for `e` to shift together. Operator arguments also need
level and modal-dependency summaries before any modal evaluation is admitted.

[Lamport, *Specifying Systems*, §§16.1.4 and 17.2](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)

## Values and admitted syntax

- `DataOperations` supplies membership, enumeration, separation, images, and
  a fixed `Data.ChoicePolicy`. `DataOperations.ofModel model` adapts the
  pure-set `Data.Model` and inherits its laws on the entire carrier. The
  evaluator itself requires no set extensionality. Set images bind one
  identifier. Rigid quantifiers support multiple plain names and groups. All bounded domains are lowered in the
  incoming scope. Bounded quantifiers and bounded CHOOSE restrict witnesses
  through the supplied membership operation. Equality is Lean equality on
  the common carrier. [Pure-set model](tla-data.md)
- `Booleans` provides TRUE and FALSE, a predicate interpretation with laws for
  those two values, and a policy for invalid operands. Equality, inequality,
  membership, nonmembership, and rigid quantification return the Boolean
  values. `BOOLEAN` enumerates the two Boolean values. IF and logical operators
  have their usual behavior on Boolean guards and operands. Absorbing values
  such as FALSE in conjunction also determine the result with a non-Boolean
  operand. The `invalid` policy supplies the result in the remaining cases.
  A predicate position in a binder uses the supplied `holds`.
  [Lamport, §§16.1.3–16.1.4](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=314)
- `ExternalSignature` lists admitted declaration IDs and expression arities.
  A used signature-only operator or positive-arity CONSTANT operator must
  match both the resolved signature and the admission table. Source
  definitions always expand from their bodies. At evaluation,
  `ExternalInterpretation` supplies a `Primitive` for each admitted ID,
  with a Lean implementation and a proof of the caller's stated contract
  for argument lists of that arity. A caller may parameterize a result over
  that contract explicitly. The API assigns no standard-module semantics
  by name.

The tagged carrier has set extensionality for recognized set values. A tagged
adapter can supply its checked membership and enumeration operations, and
test set recognition before separation and image. It must supply explicit
results for unrecognized bounds, for which the usual set-formation laws are
conditional. With tagged membership, an unrecognized bound has no members.
A bounded existential is then false, a bounded universal is vacuous, and a
bounded CHOOSE uses the choice policy's no-witness result. The tagged adapter
is a separate increment. [Tagged values](tla-tagged-values.md)

Literals, tuple binders, multi-binder images, CASE, functions, records, tuples,
and other collection syntax require future clauses. This entry point produces
a single-state data denotation. Action and temporal forms, INSTANCE, ASSUME,
theorem declarations and proof syntax are outside the checked pipeline.
The incremental scope leaves intact HourClock and collection-heavy examples
for later work.

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Examples
scripts/check-layout.sh
```

The fixture runs the existing parser and resolver, then lowers selected
definitions from two in-memory source modules and one signature module. The
test elaborator quotes the resulting terms as ordinary Lean data. The kernel
checks the witness-scope and external-admission proofs and equations for the
resulting denotations over the pure-set adapter and arbitrary valuations. A
separate equation checks that image uses an interpretation's supplied policy
on an unrecognized bound. The fixture exercises home-module lookup,
forwarding and LET capture, repeated expansion of the same binder, set image
and filtering, rigid quantification, CHOOSE, and a proved external
implementation. Guards check prime, unsupported tuples, depth
exhaustion, wrong arity, and a same-named external from a different module ID.
The parser and resolver run during elaboration, so this fixture does not
constitute a general source adequacy theorem.

[In-memory regression](../../Silmaril/Logic/Temporal/TLA/DataElab/Examples.lean)
