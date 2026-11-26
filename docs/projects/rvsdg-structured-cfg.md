# A typed grammar for structured flat CFGs

The grammar has three constructors. A leaf uses the existing typed loop
with an acyclic body. A serial link redirects two same-sort exits of one
child to the entry of the next. A branch runs a classifier, selects one
of two children, and redirects either child's exits to one shared
continuation. Both arms, the continuation, and both sides of a serial
link use the same grammar recursively. The LambdaSSA compiler emits one
actual flat `Region.cfg` by relocating typed labels at each constructor.
[Grammar and lowerer](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Defs.lean)

The inherited branch interface uses a classifier of type
`A → (M + M) + Y`. Both left injections enter the left arm with payload
`M`. The right injection enters the right arm with payload `Y`, which may
differ from `M`. All exits feeding the join carry `M`. Final labels
may carry different types. The graph has typed serial carriers at
its boundaries. The root classifier reads the active entry injection.
A `Fin 2` selector indexes the two γ children, which each receive the
carrier and one token. The existing checked splice inserts the shared
continuation once and uses the selected child's data and exact returned
token. The connectors use the existing carrier routing and preserve
the token.

`lower` constructs a numbered graph and a syntax-directed `Related`
witness. `raise` constructs the opposite fibre from a supplied
`Decomposition` containing the grammar and exact graph equality.
The certificates are indexed by syntax and numbered wiring.
The reverse fibre uses supplied structure. Automatic recognition is
available separately for the fixed loop diamond and serial families.

## Observations

`branch_agrees` takes agreement for three independently admitted
components and uses `Flat.denote_fork` and `Flat.denote_link` to
factor the actual repository denotation. The proof compares the selected
arm with its relocated flat blocks before invoking the continuation.
The induction for all grammar trees reuses the existing serial
composition law and single-loop theorem. Primitives run in source
order in one coherent `StateT σ Part` model and may be partial.
[Agreement theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Thms.lean)

Every related pair has the same finite return, including the typed
external label, payload and exact final token. Absence of finite return
also agrees. The partial observation combines blocking and infinite
feedback. The grammar covers generated layouts with acyclic
loop bodies. Arbitrary reducible CFGs, arbitrary graph renumbering and
automatic reverse recognition for this grammar remain outside the
theorem.

The regression selects an inner diamond in the left outer arm and
takes feedback in an inner loop. The outer continuation is a two-loop
serial link. The returned payload reads the token on entry to the
last loop. For input 0 the payload and final token are 123357 and
1233578. For input 3 the outer right arm skips the inner diamond,
returning 167 and 1678. For input 99 a primitive in the selected right arm is undefined, and
the checked graph has no finite return from which to start the continuation.
[Lean regression](../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Regression.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Regression'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§3 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
