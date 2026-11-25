# First-order TLA+ INSTANCE denotation

Import `Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs`. First call
`Resolution.Instances.check registry root externalLevels`. Pass the resulting
`CheckedInstances` value to `DataElab.Instances.lowerState` or
`DataElab.Instances.lowerAction`, along with the semantic external signature,
an expansion depth bound, and the selected definition's `BindingId`. Both
selectors use the level certificate paired with the resolved registry. A
`BindingId` is specific to its graph.

Select a nullary source definition, such as `Out == I!Member`. State
selection admits constant and state levels, and action selection admits
action level. The results use the existing single-state and endpoint
evaluators for the core fragment. A source definition can call generated members, including nested
and anonymous instances. Direct selection of a generated member is outside
this entry. [Replay API](../../Silmaril/Logic/Temporal/TLA/DataElab/Instances/Defs.lean) ·
[Instance resolution and level checking](tla-module-instantiation.md) ·
[Endpoint evaluation](tla-data-elab.md#checked-source-and-target-evaluation)

## Substitution and endpoints

Qualified arguments keep their resolver paths at each segment. Expansion
binds the namespace arguments first and passes the remaining arguments to the
member's home declaration. When the home is another generated member, replay
continues in the enclosing instance's frame.

A WITH replacement is expanded at its recorded host site, or through its
captured host binding for an implicit replacement. Each one reads the incoming
host frame and that namespace's formals. All replacements are expanded before
the new target frame is installed. This matters when the host and instancee
inherit the same declaration ID. Ordinary source bodies and their LOCAL
helpers still resolve references at their original home sites, within the
current instance's frame. Each invocation has its own substitutions, even
when several instances share a home declaration.

Actuals and replacements are expanded terms. A prime on the host call
or in a home definition shifts flexible reads in the substituted operand to
the target endpoint. Rigid assignments and enclosing witness values retain
their scope. Bounds and bodies inside a primed operand use the target. The
existing prime guards apply after instance expansion.
[Lamport, *Specifying Systems*, §17.8](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=352)

The original state and endpoint entry points retain their admission rules.
This entry supports the resolver's first-order expression replacements and
diagnoses operator-valued WITH. Unsupported value syntax and expansion
exhaustion report source sites. An expanded term needs the existing
mathematical value interpretation, including the caller's ID-keyed external
primitives. Temporal denotation, theorem substitution, and source proof
verification are outside this increment.

## Verification

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.DataElab.Instances.Examples \
  +Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples \
  +Silmaril.Logic.Temporal.TLA.DataElab.Examples
scripts/check-layout.sh
```

The parsed fixture expands repeated and nested calls through the production
lowerer. The kernel checks equations for the selected Boolean actions across
arbitrary source and target Boolean valuations. The same nested fixture
selects a state value and an action using a host prime. Further equations
check implicit shared IDs and simultaneous swaps. Guards check argument levels
at each segment, unsupported operator replacements, and the depth bound.
[Regression module](../../Silmaril/Logic/Temporal/TLA/DataElab/Instances/Examples.lean)
