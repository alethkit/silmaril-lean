# Typed λSSA ↔ RVSDG correspondence

The first translation fragment uses the repository's `Silmaril.Isotope.LambdaSSA.Tm`
and `Tm.HasType`. An admitted open expression is a sequence of
`let₁ (op f (var i))` bindings ending in `var j`. Each instruction has one
typed argument and one typed result. A type code denotes one port, so a
dialect can use a product type as a single operand or result. The fragment's
syntax includes neither forming nor destructuring those products.
[Admission and fibres][defs] · [Categorical theorems][thms]

`inputs` maps the ordered λSSA context to value ports using the same type
codes. `Opcode.instr` keeps the instruction and obtains its unary port
signatures from `HasTy`. `Scope.origin` maps de Bruijn zero to the newest
binding and keeps older producer numbers when appending to the table. The
entry order is the de Bruijn list order, with index zero at the first port.
The semantics compares this ordering to λSSA's choice of newest variable as
the right tensor factor.

`Related` describes the correspondence by the syntax rules for a result
wire and for an opcode with a numbered input wire and a related
continuation. It contains no semantic premises. `SSAForm` recognizes the
expression shape with typed variable positions. At the RVSDG end, `RVForm`
certifies unary primitive nodes and their typed live origins. `GraphForm`
applies this test to the typed numbered linearization. `lowerGraph` and
`raiseGraph` construct dependent pairs of target syntax and correspondence
evidence. `Related.typing` recovers repository typing for every witness.

## Model and theorem

Given the repository's λSSA `TypeModel`, each primitive must have a value
arrow `f` whose image under the distributive Freyd functor `J` is its
`InstructionModel` denotation. The RVSDG model wraps these same value
arrows with the singleton port-product unitors. `GraphRelated.sound` applies
to any relation witness. It constructs a structural λSSA `Denotes` witness
whose image agrees with the direct RVSDG graph arrow after applying the input
context map and removing the trailing unit on the result. In a model with
the existing `TypingCoherent` hypothesis, `GraphRelated.denote_eq` identifies
the standard chosen λSSA denotation. The proof covers the acyclic rules of
the interface, so a strong Elgot Freyd model can instantiate it without using
iteration.

## Multiway selector boundary

A λSSA selector for `n + 1` arms is a right-associated sum of `n + 1`
copies of unit. `selectorLiteral` constructs a typed tag in actual λSSA
syntax. Arm zero is the left injection, each successive right injection
advances one position, and the final unit marks the last arm. This agrees
with the RVSDG predicate's in-range index. The interpretation of the λSSA
sum and the RVSDG selector object each satisfy the coproduct universal
property for `Fin (n + 1)` copies of the tensor unit. `selectorIso_tag` proves
that the canonical isomorphism preserves each arm number. The types instance
of the RVSDG model uses `ULift (Fin (n + 1))`.
[Selector encoding][selector]

The bidirectional theorem in this increment covers unary straight-line
bindings and variable returns. Multiway γ needs a separate relation rule
that lowers a left-first spine of λSSA cases, sends each arm an explicit
ordered capture tuple, and closes the unit payload binder. This increment
checks the selector boundary. It leaves case-spine lowering, arbitrary
expressions, state ports, multiple exits, CFG restructuring, ordered effects
and iteration open. The following institution work can use the typed
correspondence as the syntax layer and the graph soundness theorem at the
model boundary.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.LambdaSSA.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Selector.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Selector.Thms'
```

The fixture uses two distinct base types, an argument wire, an output shared
by two instructions, and a return from an older binding. It also checks
the ordered selector encoding at arity three. [Fixture][fixture]

The exact studied versions and PDF SHA-256 digests of Reissmann et al.,
*RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
and Ghalayini and Krishnaswami, *The Denotational Semantics of SSA* (2024),
are pinned in the categorical milestone. The relevant passages are RVSDG
§§4.1.1–4.1.2, 5.1.2 and 5.2.2 and λSSA §§3 and 5.3.
[Scholarly source pins](rvsdg-categorical.md#sources)

[defs]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Defs.lean
[thms]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Thms.lean
[selector]: ../../Silmaril/SSA/RVSDG/LambdaSSA/Selector/Thms.lean
[fixture]: ../../tests/ssa/RVSDGLambdaSSA.lean
