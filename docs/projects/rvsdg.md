# Regionalized value state dependence graphs

`Silmaril.SSA.RVSDG` formalizes the typed acyclic fragment with simple nodes
and multi-way γ nodes from Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers* (2020).
The source is arXiv:1912.05036v2, §§4, 4.1.1–4.1.2, 4.3 and 5.1.3.
The versioned PDF has SHA-256
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2) ·
[DOI](https://doi.org/10.1145/3391902)

## Representations and theorems

[Defs](../../Silmaril/SSA/RVSDG/Defs.lean) defines two representations over
a shared typed port vocabulary.

- `Term` is inductive let syntax. A let defines an ordered tuple of outputs and
  extends lexical scope for the rest of the region.
- `Graph` stores a vertex table with local finite node IDs, a separate table of
  child graphs keyed by vertex and arm, and a tuple of result edges. A node input
  or region result is the user of exactly one edge. An origin names a typed
  argument port or an output port of a local vertex and can have any number of
  users. `Graph.producer_lt` shows that each node-to-node edge points from a
  lower-numbered producer to a higher-numbered consumer in its region.
- A primitive's indexed opcode determines its input and output types. A γ with
  `n + 2` arms receives a selector in `Fin (n + 2)` and a tuple of entry ports.
  Its arms share the entry and exit signatures, and only the selected arm runs.
  Each arm has fresh local scope and receives outside data through its arguments.
  A whole region starts with the empty prefix of local node signatures.

[Thms](../../Silmaril/SSA/RVSDG/Thms.lean) states
`Term.toTerm_toGraph` and `Graph.toGraph_toTerm`. They are inverse translations
at a fixed numbering in every region of the hierarchy. The output signatures,
wire addresses, result order and branch order are preserved exactly. The vertex
IDs already give a topological order. Equality modulo vertex renaming or
permutation of independent vertices, and admission or scheduling of arbitrary
labelled DAGs, are future work.

`Term.run` interprets lets in lexical order. `Graph.run` reads the graph table
directly and fires each vertex once per active region in node-number order.
`Graph.run_toTerm` and `Term.run_toGraph` give equality of returned port tuples
for every input and total deterministic primitive model. Each active region
runs all of its vertices. The observation consists of the returned tuple,
including any returned state. State sorts are distinct from value sorts, and
state sequencing is explicit through wires. Like value ports, state origins
permit fan-out and may be unused. An operation has only the effects carried
by its input and output state values in this model.

## Reproduce the checks

From the repository root with its pinned Lean toolchain:

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDG.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Thms
```

The [fixture](../../tests/ssa/RVSDG.lean) constructs a graph directly as tables.
A state wire sequences a write, a three-way γ, and a read. The test checks
all three state histories, including the pass-through branch, and reads a
single value output through two result ports. It also checks an independently
constructed term and the impossibility of sourcing a value from a lone state
argument in an empty scope. For the axiom audit, import the theorem header
and use `#print axioms` on the five public theorems.

## Next milestone

Use the same fragment for a typed, coloured Petri-net semantics. Key places by
local region and user port, with one place per edge user so fan-out can produce
one token per edge. Use pending/done control places for each active vertex.
On region entry, seed argument-user places from the input tuple and mark its
vertices pending. A primitive transition consumes its pending token and all
input tokens, evaluates `Model.run`, and produces output-user tokens and a
done token. A γ consumes its selector and entry tokens, records the selected
arm in a waiting place, and activates that arm alone. Its exit transition
consumes the selected region's result tokens and done tokens, then publishes
the γ outputs. Region completion requires both all result tokens and all done
tokens, including for vertices whose outputs have no users.

The interface should expose `initial` for a graph and input tuple, a firing
relation `Step` on typed markings, and `Finishes` for reachability of a completed
root with a given result tuple. Prove
`Finishes m g input output ↔ g.run m input = output`. For soundness, track
the unique activation of each pending vertex and prove agreement of each
produced token with the numbered evaluation. For completeness, construct a
run from the vertex numbering using `Graph.producer_lt`, recursing into each
selected arm. The same net is a candidate for proving invariance across
topological numberings of a labelled hierarchical DAG after defining
renaming of endpoints and corresponding markings.

## Remaining RVSDG constructs and later semantics

- **θ (§4.1.3).** Match the loop's input, output and body argument signatures.
  The body returns a continuation predicate followed by the updated loop
  tuple. Evaluate the body at least once and distinguish finite return
  from divergence. Extend the firing semantics with feedback at the region
  boundary while preserving the DAG invariant inside each iteration.
- **λ and apply, δ, ϕ, ω (§4.2).** Add explicit capture and callable signatures
  for function bodies and calls, capture and a single initializer result for
  globals, and recursion arguments paired with definition results for mutual
  recursion. Use a single root ω region for translation-unit imports and
  exports. Add linking and call observations alongside these interfaces.
- **Denotations, translations and institutions.** First prove agreement with
  a monoidal interpretation of the acyclic operations. Extend to ordered
  effects and iteration using the existing premonoidal and Elgot interfaces.
  Specify both directions of SSA/RVSDG translation as relations on typed
  open regions and prove preservation for each related pair under a shared
  observation, including returned state and divergence where defined. A
  construction or destruction algorithm should inhabit the appropriate fibre.
  For the dialect institution, use signature-preserving opcode maps,
  relabelling of sentences and model reducts. Prove that evaluation commutes
  with reducts before packaging the satisfaction condition.
  [Existing SSA, Elgot and institution interfaces](ssa.md)
