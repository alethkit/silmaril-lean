# Quint export fixtures for TLA+

For BoundedCounter and BitPair, use the checked-in TLA+ files as concrete inputs
and [oracle.json](oracle.json) as the expected initial states and complete
one-step relations on the listed finite domains. Each state array follows the
order in `variables`. Each transition is a pair of state arrays in source,
destination order. The exported operators to check are `q_init` and `q_step`,
which alias `init` and `step`.

Run `make tla-import-check` for the Lean import regression over these files.
[Import API and checks](../../../docs/projects/tla-quint-import.md)

| Fixture | Bounded states | Initial state | Raw `q_step` successors |
|---|---|---|---|
| [BoundedCounter](BoundedCounter.tla) | `0, 1, 2` | `0` | `0 → {1}`, `1 → {2}`, `2 → {}` |
| [BitPair](BitPair.tla) | `{0,1} × {0,1}` | `(0,1)` | `(0,0) → {(0,0),(0,1)}`, `(0,1) → {(1,0),(1,1)}`, `(1,0) → {(0,0),(0,1)}`, `(1,1) → {(1,0),(1,1)}` |

Both right-hand sides in BitPair read the source state. The false choice
swaps the bits, so in particular it sends `(0,1)` to `(1,0)`. The true
choice sends `(x,y)` to `(y,1-x)`. All listed states are reachable from the
respective initial state. The finite domains are test bounds on integer
valuations.

## Concrete syntax and dependencies

- Both files use a module header and footer, `EXTENDS`, singular `VARIABLE`
  declarations, block comments with Apalache `@type` annotations, and nullary
  definitions with `==`. The exporter lowers Quint initialization assignments
  to unprimed equality. Its step expressions use postfix prime, infix `:=`,
  conjunction `/\`, and the integer operators `<`, `+`, and `-`.
- BitPair uses a bounded existential `\E flip \in { FALSE, TRUE }:` for
  `oneOf`, with set enumeration, Boolean literals, and a parenthesized
  `IF … THEN … ELSE …` expression in the second update.
- Both files declare `EXTENDS Integers, Sequences, FiniteSets, TLC, Apalache, Variants`.
  Arithmetic and order resolve through `Integers`, which extends `Naturals`.
  `Apalache` defines `__x := __e == __x = __e`, so this operator constrains a
  successor value by equality. `Sequences`, `FiniteSets`, `TLC`, and `Variants`
  contribute no operators used by the fixture bodies. The bundled SANY in
  the pinned Apalache distribution resolves all six modules.
  [Apalache module](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/src/tla/Apalache.tla)
- These two exports stop at state and action predicates. The oracle includes the
  self-loops produced by BitPair at `(0,0)` and `(1,1)`. A later spec using
  `[][q_step]_vars` with the full state as `vars` adds a self-loop at each state
  by the bracket semantics, including the blocked counter state `2`. Neither
  export adds that bracket or a fairness clause.

## Temporal export

[ServiceCycle.qnt](ServiceCycle.qnt) starts at phase `0` and enters phase `1`.
From `1` it can bypass service at `2` or take `service` to `3`. Both branches
return to `1`. The pinned pipeline emits `safe`, `weak`, and `strong` in
[ServiceCycle.tla](ServiceCycle.tla), whose bytes go directly to the Lean
importer. The source uses `always(step.orKeep(phase))` for the full-state
bracket and `weakFair(service, phase)` and `strongFair(service, phase)` for
fairness. `atStart` is a state predicate spelling out the initial phase.
[Quint operator semantics](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/builtin.qnt#L630-L774) ·
[Apalache conversion](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/tla-io/src/main/scala/at/forsyte/apalache/io/quint/Quint.scala#L634-L649)

| Infinite phase sequence | `safe` | `weak` | `strong` |
| --- | --- | --- | --- |
| `0 · (1, 3)ω` | Holds | Holds | Holds |
| `0 · (1, 2)ω` | Holds | Holds | Fails |

[The Lean regression](ServiceCycle.lean) compares the complete parser result
with the tree used by the proofs and exercises `Import.importTemporal` on all
three names. It proves equivalence to reference predicates on integer phase
sequences. Those predicates use the five raw edges read from the Quint
branches, equality for a stutter, and enablement of the visible service edge
exactly at phase `1`. The proofs build behaviors indexed by all natural numbers.
In the service cycle the edge `1 → 3` occurs after every time bound. In the
bypass cycle phase `2` recurs, so service is never continuously enabled from
any point. Phase `1` also recurs, and the service edge never occurs. The proof
of enablement uses the explicit successor `3` in the full typed state space.

### Export and oracle limits

- Replacing `atStart` in `safe` with the assignment action `init` makes
  `compile --target=tlaplus` fail with `QNT409`. The init-to-predicate pass
  rejects using the selected init action from another declaration.
  [Pinned init conversion](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/ir/initToPredicate.ts#L121-L151)
- In this fixture, `Set(phase)` as the fairness observation exports as
  `WF_({phase})(service)` or `SF_({phase})(service)`. Set-valued observations
  and a plain state formula such as `always(phase >= 0)` are outside the
  Lean fragment. The latter exports as `[](phase >= 0)`.
  [Lean temporal fragment](../../../docs/projects/tla-elaborator.md#temporal-definitions)
- The Quint TypeScript interpreter returns `QNT501` for these temporal
  builtins. The raw interpreter oracle still covers BoundedCounter and BitPair.
  For ServiceCycle, the reference predicates use the documented Quint semantics
  and TLC checks the generated TLA+ formulas. The regression covers this fixture
  and the selected behaviors. General translation correctness remains open.
  [Pinned interpreter dispatch](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/runtime/impl/builtins.ts#L750-L765)

## Provenance and opt-in checks

The Quint sources and oracle are original Silmaril fixtures under the
repository's MIT license. The `.tla` files are their byte-for-byte exporter
output, including whitespace and type comments. No upstream examples or
support modules are copied here. [Repository license](../../../LICENSE)

The exporter is Quint at commit
`95141d4691cce7e60104bdfcbc1d1b074f1cb789` (reports `0.34.0`), built from
its upstream lockfile. Quint sends flattened, analyzed JSON to Apalache's
TLA+ export RPC. The backend and the SANY/TLC distribution come from the
same Apalache `0.62.4` release (commit
`7954daf7563a69cce9d0b89c8542e40bf46f7c6e`). Both upstream projects are
Apache-2.0. [Quint exporter](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/quint/src/compileToTlaplus.ts)
· [Quint license](https://github.com/informalsystems/quint/blob/95141d4691cce7e60104bdfcbc1d1b074f1cb789/LICENSE)
· [Apalache release](https://github.com/apalache-mc/apalache/releases/tag/v0.62.4)
· [Apalache license](https://github.com/apalache-mc/apalache/blob/7954daf7563a69cce9d0b89c8542e40bf46f7c6e/LICENSE)

From the repository root, prepare the tools outside the checkout. Verified on
Linux x86-64 with Node `26.13.1`, npm `11.20.0`, and OpenJDK `21.0.13.1`.
The setup downloads sources, locked npm dependencies and the Apalache
archive. The checker uses local tooling and a loopback gRPC connection.
Reading the fixtures requires only the checked-in files.

```sh
tools_dir=$(mktemp -d)
git init -q "$tools_dir/quint"
git -C "$tools_dir/quint" fetch --depth=1 https://github.com/informalsystems/quint.git \
  95141d4691cce7e60104bdfcbc1d1b074f1cb789
git -C "$tools_dir/quint" checkout --detach FETCH_HEAD
npm --prefix "$tools_dir/quint/quint" ci

curl --fail --location --output "$tools_dir/apalache.tgz" \
  https://github.com/apalache-mc/apalache/releases/download/v0.62.4/apalache.tgz
tests/semantics/tla-quint/check.sh --check "$tools_dir/quint" "$tools_dir/apalache.tgz"
```

The checker requires archive SHA-256
`8ac8488422c30d552735bae11b92a2d014d8e02e8608702acc08f9a2d8a9abb2`.
It runs Quint's `compile --target=tlaplus` with explicit module, init, step
and backend flags. It compares the export bytes and verifies [SHA256SUMS](SHA256SUMS).
Use `--write` in place of `--check` to refresh the exports and hashes after
the semantic checks pass. The oracle is maintained as explicit expected values.

The semantic checker evaluates `init` in the pinned Quint TypeScript
interpreter, then injects each listed source valuation into the interpreter
and evaluates the original `step`. For BitPair it drives the single draw
through positions 0 and 1, checking that the evaluator requests exactly one
draw with bound 2 per evaluation. Each successful evaluation shifts the
complete next-state registers and checks the resulting valuation. The
counter's disabled step at `2` evaluates to false.

Separately, TLC invokes SANY on the generated files and exhausts the
reachable graph of each raw fixture with `INIT q_init` and `NEXT q_step`.
The checker compares the initial labels, all reachable valuations and every
edge in TLC's DOT dump to the same oracle. TLC's `-deadlock` flag disables
the deadlock diagnostic so the counter's expected empty successor set is
accepted.

For the temporal fixture, [ServiceReplay.tla](ServiceReplay.tla) is an
authored TLC driver that extends the generated module. Its two deterministic
replay actions choose a cycle and its own weak fairness rules out stopping in an
infinite stutter. Finite stuttering is still allowed. TLC checks the exported
declarations as properties of these replay behaviors. The checker requires
success for `safe`, `weak`, and `strong` on the service cycle and for `safe`
and `weak` on the bypass cycle. For `strong` on the bypass cycle it requires a
temporal-property violation and checks the JSON counterexample, including the
back edge from `2` to `1`. TLC explores the replay graphs with state
fingerprinting. The Lean proof establishes the two infinite-run judgments
independently of TLC.
