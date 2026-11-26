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
The recognizer constructs that decomposition directly from the typed
numbered graph, as described below.

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
loop bodies. Arbitrary reducible CFGs and graph renumbering remain
outside the theorem.

The regression selects an inner diamond in the left outer arm and
takes feedback in an inner loop. The outer continuation is a two-loop
serial link. The returned payload reads the token on entry to the
last loop. For input 0 the payload and final token are 123357 and
1233578. For input 3 the outer right arm skips the inner diamond,
returning 167 and 1678. For input 99 a primitive in the selected right arm is undefined, and
the checked graph has no finite return from which to start the continuation.
[Lean regression](../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Regression.lean)

## Recover from a numbered graph

`Reverse.candidate` scans the actual outer vertex order and descends
into each γ arm. It reuses the local θ parser for loop bodies. Serial
connector opcodes identify the handoff types. The left arm's entry
connector and the two exit connectors supply the arm and continuation
interfaces, even when the two arms enter at different types.

The emitted order of serial cuts can represent several associations.
`Reverse.Normal` fixes a right-associated serial form in which a
serial link starts with one θ and a fork owns the rest of its scope
as its continuation. The parser chooses this form independently
inside each arm. The local loop parser right-associates instruction
sequences. Certification re-emits the candidate and compares the
full typed graph recursively, including selector operands, captured
arguments, results, and token origins.

`recover_isSome_iff` characterizes acceptance as literal equality with
the emitted graph of some outer normal form. It allows arbitrary sequence
association and nested acyclic choices inside those loops. When the
local bodies also use the parser's association, `recover_generated`
identifies the recovered source exactly. Other outer associations can
be accepted when their graphs coincide with the normal emission. The
regression checks this property on a three-loop serial chain emitted
with left association. A general graph equality theorem for rebracketing
all outer compositions is outside the completeness statement.

The recovered CFG has the same two observations and the same absence of
a finite return as the nested-diamond fixture. A type-correct mutation
redirects the shared tail's first token to the graph entry while retaining
the γ payload. The label parser still returns the original candidate and
certification rejects the graph.
[Reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Reverse/Thms.lean)

## Compile through the outer normal form

`Normalization.normalize` covers every admitted structured source. It
passes a serial suffix through a preceding sequence and into a fork's
existing shared continuation. The two arm scopes stay local to the fork.
The type of the operation preserves the boundary carrier types and the
ordered vertex signature table. Applying it to a source already written
in `Reverse.Normal` returns that normal form.

`denote_normalize` proves equality of the repository's flat
`Region.denote` in the coherent monadic Elgot interface. The proof uses
the actual flat fork and flat link laws and reassociates binds. In the
partial-state model, `compile_returns_iff` and `compile_undefined_iff`
compare the original flat CFG with the newly emitted graph, including
the typed exit and exact final token. Every result of reverse recovery
on that emission has the original CFG's partial denotation.

`Normalization.compile` emits the explicit normal layout. The existing
recognizer is complete on its output for every `Syntax` witness.
`decideNumbering` uses full typed graph equality to check the earlier and
normal emissions for a particular source. The regression checks literal
equality on a fork followed by a composite suffix, where stages 8 and 9
move into the fork's continuation after stage 7. On input 0 the graph
returns payload 123357 and token 12335789. Input 99 has no finite return.
The compiler and round-trip theorem apply independently of the per-source
comparison. A universal equality theorem for the two emissions would
require a syntactic associativity law for checked splice and origin
relocation. The existing splice law gives denotational composition.
[Normalization API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/StructuredCFG/Normalization/Thms.lean)

## Two levels of feedback

`NestedFeedback.lower` is a separate forward entry point for a flat
two-block region with an outer header of type `A`, an inner header of type
`B`, and one typed external label of type `D`. The outer block applies
`A → B` and jumps to the inner block. The inner block applies
`B → K ⊕ B` and either restarts itself or sends the completed `K` to a
`K → D ⊕ A` decision within that block. The decision exits at the external
label or restarts the outer block. The three arrows are existing typed
LambdaSSA instructions. The loop nesting is determined by this source
witness, with no general cycle recognition step.

The numbered outer θ contains the entry instruction, the inner θ, and
the final decision instruction. The inner θ receives the entry
instruction's live token, and the final decision reads both outputs of
the inner θ. Each restart uses the activation's returned token.
Coproduct carriers encode the different entry and exit payload types,
and the θ tag selects exit or restart. The shared partial instruction
model performs one source instruction per primitive. The constructor
`Related.generated` supplies the source typing and existing single-live-token
admission for the emitted graph.

`denote_rounds` derives nested iteration from actual flat
`Region.denote` in a coherent monadic Elgot model using codiagonal,
naturality and pure uniformity. In `StateT σ Part`, every relation witness
preserves and reflects finite graph returns at the typed external label,
including the exact final token. The undefinedness theorem compares
absence of a finite return. The fixture follows an inner restart in each
outer activation and an outer restart, then reads the token into the
returned payload. A second input stays in the inner loop and has no
finite derivation.
[Nested feedback API](../../Silmaril/SSA/RVSDG/LambdaSSA/NestedFeedback/Thms.lean)

`NestedFeedback.Reverse.recover` takes the typed numbered graph and
its dialect. It reads both θ regions, infers `B` and `K` from the
opcode roles, and checks the three instruction types against the
signature. It reconstructs the source and accepts only if re-emission
matches the actual graph recursively, including every typed port,
operand, child and result address. Success returns a flat region with
a relation witness indexed by that input graph. Every canonical
emission recovers its original region and both internal types.

The recovered CFG has the same finite observations and exact final
token in the coherent partial-state model. The regression reuses both
nested-feedback cases and checks a mutation that replaces the inner
θ's returned token at the decision with the outer entry token. The
mutation leaves the payload and both θ shapes intact. Parsing succeeds
and full certification rejects the differing token address. This
recognizer accepts precisely the literal numbered images of the
two-header shape. It uses the graph's outer boundary types and infers
the inner types. Other loop layouts, arbitrary renumbering, and
general CFG structuring are outside this API.
[Nested feedback reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/NestedFeedback/Reverse/Thms.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Thms +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Regression'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Normalization.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms +Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Regression'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms
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
