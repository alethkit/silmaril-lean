# Interprocedural RVSDG interfaces

This graph slice follows Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers*,
arXiv:1912.05036v2, §§4.2.1–4.2.4 and Definitions 4–8. The versioned PDF
has SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The type vocabulary extends value sorts with callable signatures and
global identities. State and control keep their existing typed ports.
The translation-unit graph uses the established scope and origin rules.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Defs.lean)

- **λ and apply.** A λ has one function output and a body in the compositional
  θ fragment. Its context variables pair its ordered inputs with the prefix
  of its body arguments. Its formal call arguments follow that prefix.
  `Lambda.close` reads the context wires from the parent and stores those
  values with the body. `Closure.enter` prepends the saved values to the
  explicit arguments. Apply is a tagged simple node whose first operand is
  a compatible callable and whose remaining operands and results match its
  signature.
- **δ.** A δ captures context for an acyclic initializer. That region returns
  a single right-hand-side value. The outer output has the corresponding
  global-identity type, allowing a caller or another initializer to capture
  the global as an entity.
- **φ.** A φ has a λ-only child region. Its arguments contain the context
  variables followed by one recursion argument per member. At each member
  position, the recursion argument, the region result and the φ output share
  that member's function type. `Phi.resultOrigin` routes the sole output of the
  λ at that position to the region result. A λ may capture any recursion
  argument, including its own identity or a later member's identity.
  Physical capture edges between definitions still require earlier
  producers. `Phi.enter` arranges the context values and externally
  supplied recursive tuple at their argument ports.
- **ω.** The root is a translation unit with one region and no outer ports.
  Its region arguments represent imports and its region results select
  exports from the local graph.

The fixture defines two mutually recursive functions that capture each
other's recursion arguments and call through those arguments. The φ
captures a δ output. An ordinary λ captures a φ output and the global,
and the ω exports both members, the ordinary λ and the global. Symbolic
values check positional closure binding alongside the typed graph checks.
[Scoping theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Thms.lean) ·
[Fixture](../../tests/ssa/RVSDGInterprocedural.lean)

## Inductive presentation and graph correspondence

`ModuleTerm` is a sequence of typed λ, δ and φ bindings followed by
the export tuple. A let extends the local scope with its declared output
ports. `OmegaTerm` binds the entire region at the import signature,
with an empty local prefix. For λ and δ, the bodies use the existing
inductive region syntax. Inside φ, `Definitions` is an inductive list of
typed λ definitions whose scopes are indexed by member position. All
recursion arguments are available at every definition, while physical
outputs are available only after their bindings.

The translations use the existing `Lambda`, `Delta`, `Phi` and `Omega`
graphs. The graph-to-term direction walks the body tables in number order
and the φ table in member order. The converse collects the bindings into
those tables. Lean proves both round trips for each of the four forms,
at the given numbering. Capture wires, φ member positions, and module
result wires are preserved exactly. These are syntactic equalities.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Terms/Defs.lean) ·
[Theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Terms/Thms.lean)

The [term fixture](../../tests/ssa/RVSDGInterproceduralTerms.lean) authors
a translation unit as inductive bindings, checks its numbered graph table,
round-trips both presentations, and checks the translated endpoints for
the mutual recursion arguments and exports.

## Semantic boundary

The [first operational slice](rvsdg-module-linking.md) links φ-free
modules and invokes the linked closures. A φ semantics must provide a
recursive tuple whose callable components resolve to the corresponding λ
closures entered under that very tuple. The acyclicity theorem here
applies to physical capture edges and leaves recursive calls to that
semantics.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterprocedural.lean
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGInterproceduralTerms.lean
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms
```
