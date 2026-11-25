# Closed Python integer bodies

The core implements the first Python body from the
[Python SOS proposal](https://github.com/hiloopai/silmaril-lean/pull/2131).
It models a zero-argument function after entry. A `Body` contains the
expression of its single return statement. Expressions use signed
mathematical integers and two binary operators, addition and floor division.
Evaluation proceeds left to right. Division by zero propagates an uncaught
`ZeroDivisionError`. The model has no host services, resource bounds, or
object protocol.

The arithmetic and return behavior follows the Python 3.12.13 Language
Reference. The expressions chapter (§§6.7 and 6.16) has HTML SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
The simple statements chapter (§7.6) has HTML SHA-256
`817344777aad7579f74f9260bb2f41e3c8368ae5dce0fe083c2a458af3504721`.
[Expressions](https://docs.python.org/release/3.12.13/reference/expressions.html)
· [The return statement](https://docs.python.org/release/3.12.13/reference/simple_stmts.html#the-return-statement)

## Entry and observations

A profile checks the whole expression at entry. The arithmetic profile
enables both operators, and the addition profile enables only addition.
`Body.start?` computes the initial state for an admitted body. If an
unsupported state is supplied directly, the `WithUB` policy marks it and
disables its steps and observations. A rejected body has no entry and
therefore no reachable UB or finite outcome. The labelled machine uses the
same profile guard. Its arithmetic steps are silent, and the one exit
label carries the return value or exception. The generic finite outcome for
either exit is `Outcome.returned` with an `Except Exception Int` payload.
[Definitions](../../Silmaril/Languages/Python/Core/Defs.lean)

The inductive `Step`, the one-redex selector and the structural
`Expr.eval` are separate definitions. The proofs establish exact agreement
on primitive steps, preservation of the structural result and admission,
progress, terminal observations, and a decreasing count of remaining work.
For admitted bodies the model has one finite outcome, one visible exit
trace and no divergence. The bounded runner reports exhaustion when it
needs another transition. The initial state's budget suffices for the exact
outcome. [Theorems](../../Silmaril/Languages/Python/Core/Thms.lean)

## Elaboration boundary

A future shared Python/Starlark front end can elaborate its syntax into the
language-specific body and check profile admission at that boundary. For
Python, the elaborator must resolve the source function body and preserve
literal values, operator grouping and operand order. Elaboration errors
occur before operational initialization. The Python core depends on the
operational-policy API in `Semantics` and can be used independently of
Starlark or the SOS institution.

The next rule correspondence can use a downstream fixture to present
`Expr.Step` and `Step` independently as finite positive rules and prove
both directions through the shared SOS API. A separate parity increment
can check signed arithmetic, nested operand order and exceptions against
CPython before adding variables and scope elaboration. A completion-policy
comparison and a guarded Wasm adapter need their own observation and
representation contracts.
