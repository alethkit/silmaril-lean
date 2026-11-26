# Checked header operand substitution for cyclic GVN

`HeaderUse.redirect?` takes a certified cyclic activation view, a
partition, a producer of the actual `Loop.Graph.header`, and one typed
operand port of that producer. The caller supplies the original source,
a proposed same-sort representative, and a typed wire in the consumer's
prefix. The checker decides whether those sources match the actual use
and the available wire. On acceptance the edit changes exactly that
tuple position. The rewritten table uses the original signatures,
producer order, and output addresses.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/HeaderUse/Defs.lean) ·
[Activation invariant](sea-of-nodes-gvn-cyclic-activation.md)

## Availability and preservation

- `check_eq_true_iff` characterizes acceptance. The partition is stable,
  the two sources have equal typed class keys, and their completed-header
  wires match the lifted old operand and lifted replacement, respectively.
  The replacement's type places it in the prefix before the consumer.
  Lifting that wire to the final scope must give the representative's
  actual typed address, so a different earlier wire cannot certify a
  later equivalent producer.
- `redirect_initial` gives the same initial latch tuple. For each
  `redirect_step`, the shared old tuple must satisfy the original
  loop's class invariant. Equal class values in the original completed
  header give equal operand reads in the consumer's prefix. The selected
  primitive therefore receives the same inputs, and its unchanged suffix
  evaluates to the same header values. The rewritten guard and full step
  agree, including the entire next latch tuple on a backedge. The original
  step preserves the class invariant on that common tuple.
- `redirect_evalBackedges` and `redirect_returns` lift this recurrence
  to every evaluator budget and the finite-return relation, for all
  typed inputs and pure total models.

The simulation relates the actual original and rewritten loops at a
common latch tuple. It uses the original view's invariant and equal step
outcomes, so the caller supplies one certified view of the original graph.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/HeaderUse/Thms.lean)

## Regression and scope

A two-operand guard at header position 2 initially reads producer 0
twice. Rewriting its second operand to producer 1 changes that occurrence
while retaining the first. The fixture takes two backedges and returns 3
in the rewritten loop. Producer 3 is in the same stable class as
producer 0 and is bound after the guard. The checker rejects it for
every supplied prefix wire. It also rejects a claimed original source
whose address differs from that of the actual operand.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/HeaderUse/Regression.lean)

This API handles one header operand per call. It uses a supplied prefix
wire and leaves representative search and feedback-column edits
separate. Deleting a producer additionally requires showing that every
surviving use, including the guard, result, and feedback columns, has a
valid routed address and that the shortened table preserves those reads.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Regression
```

## Sources

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2, supplies the ordered
cyclic congruence used here. The Rice PDF has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice record](https://hdl.handle.net/1911/16807) ·
[Rice PDF](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content)

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
§§2.1–2.4 and §3.1, relates use availability to code placement and replaces
uses of a redundant computation. Here the typed, ordered header provides
a concrete prefix at one use, and the activation proof supplies the value
agreement at that use.
[Proceedings](https://doi.org/10.1145/207110.207154)
