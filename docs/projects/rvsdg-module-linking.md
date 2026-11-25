# Linking and invoking RVSDG modules

This slice implements the λ/apply, δ and ω cases of Reissmann, Meyer,
Bahmann and Själander, *RVSDG: An Intermediate Representation for
Optimizing Compilers*, arXiv:1912.05036v2, §§4.2.1, 4.2.2 and 4.2.4.
The versioned PDF has SHA-256
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The machine supplies total primitive operations over typed colours.
A λ vertex reads its context wires and produces a closure containing the
captured colours and checked body. Apply calls that closure on the
remaining inputs. Invocation prepends the captures to the supplied
arguments and executes the body. Calls inside the body use the same
invocation rule. γ enters only the selected arm. θ repeats the completed
body with a fresh local environment and the updated carried tuple.

A δ runs its acyclic initializer at link time, using its context wires.
The single initializer result is stored in a global colour with the
supplied unit ID and the vertex's local number. The identities are
relative to the numbering, and distinct translation units need distinct
IDs. Globals are initialized values in this model. Any access operation
is supplied by the primitive machine. There is no shared mutable store.

The graph linker visits the ω vertex table in number order; the term
linker visits the bindings. Both start with an explicit typed import
tuple and read the export result wires in order. `wireImports` builds
a client's import tuple from a provider's exports. The linker succeeds
exactly for φ-free modules, given the typed import tuple and total
primitive machine. Lean proves that the two presentations link to
the same export tuple, including the saved captures, bodies and global
identities.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Thms.lean)

Invocation has two separate bounds. Call depth counts the current
activation and is decreased at each nested call. The loop bound counts
body activations per θ invocation. Lean proves that increasing either
bound preserves every successful result. Failure at a bound leaves
termination undecided. The current theorem about totality concerns
linking. The operational slice leaves recursive closure environments,
name-based linking, and unbounded call adequacy for later work.

The fixture links a provider whose δ initializes a captured global
from an import, wires an exported function into a client, and calls the
client's exported wrapper at depth two. The imported closure reads the
initialized global and returns an updated state. The test also checks
the global's identity, depth exhaustion, graph/term link agreement,
and rejection of φ.
[Fixture](../../tests/ssa/RVSDGModuleLinking.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGModuleLinking.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Thms'
```
