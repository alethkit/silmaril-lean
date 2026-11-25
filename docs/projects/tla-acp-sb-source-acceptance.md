# Pinned ACP_SB state denotations

The fixture proves exact graph-schema equations for `Init` and `TypeInv`
from intact ACP_SB. Under the explicit model premise
`participants.asSet = some P`, the initial-state denotation implies the
type invariant at the same state. All other rigid values, flexible
valuations and adapter policies are arbitrary.

## Source and selection

The source is the upstream ACP_SB example at TLA+ revision
`bc1b506bdcad80bb518bf3776a9161c34ff0fc4c`, under
`tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla`.
Its SHA-256 is
`a62fedef4725c150efd03f5a864bb607f2f3960686b518792144e1d781c6de89`.
[Pinned source](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/test-model/examples/acp/ACP_SB.tla)

The native parser reads the hash-verified file. `Resolution.Instances.check`
resolves and level-checks the complete module and retains all 40 source
units. `Collections.lowerState` selects the original nullary state
definitions by their IDs at units 7 (`Init`) and 4 (`TypeInv`), counting
from zero. Both selections use that same registry with empty external
signatures. The selected expansions are quoted as Lean data, and their
validity proofs are checked by the kernel. The action and temporal
definitions are covered by the whole-module level pass.
[Resolution](tla-acp-sb-resolution.md) · [Collection lowering](tla-data-elab.md#state-level-collection-expressions)

## Exact graph schemas

Under the set-shape premise, each state predicate holds precisely when
the two flexible values have the following shapes.

- `participant` is a graph with domain exactly `P`. Each output is a record
  with the five keys `vote`, `alive`, `decision`, `faulty` and `voteSent`.
  The field bounds are the ones in the selected source definition.
- `coordinator` is a record with the six keys `request`, `vote`, `broadcast`,
  `decision`, `alive` and `faulty`. The first three fields are graphs whose
  domains are exactly `P`. Their ranges and the remaining three field
  bounds come from the selected definition.

The Lean equations state exact record domains and per-field lookup membership,
using the [tagged record-set laws](tla-record-sets.md) and [function-set
laws](tla-functions.md). The proof of `Init → TypeInv` reuses the same
participant graph and coordinator record. It preserves their domains and
widens each field range. The two coordinator schemas list their fields in
different orders and have the same exact key set.

DataBridge supplies rigid and flexible lookups by declaration identity and
lifts the selected predicates to General TLA state formulas. The equations
and implication hold at any instant of an arbitrary behavior with one rigid
valuation. The checked implication is a state obligation.
[DataBridge](tla-data-bridge.md)

## Reproduce

```sh
python3 -I tests/semantics/tla-acp-source-acceptance/check.py
```

The driver reuses the native parser fixture pin and temporary download
verification. It builds the fixture's dependencies with warnings as
errors and runs the Lean checks, including the axiom audit.
[Driver](../../tests/semantics/tla-acp-source-acceptance/check.py) · [Lean fixture](../../tests/semantics/tla-acp-source-acceptance/ACP_SB.lean)
