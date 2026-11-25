# Positive SOS for closed Python arithmetic

The presentation generates ground rules from a finite family of schemas over
exact integers and the closed Python core AST. Its judgment names distinguish
primitive arithmetic, expression reduction and a labelled machine edge.
Addition and the two floor-division cases are primitive facts. A nonzero
divisor is a side condition on the successful-division schema. An expression
contraction requires a primitive judgment, expression contexts require a
subexpression judgment, and a silent machine step requires a reduction
judgment. Return and uncaught-exception emission are terminal control steps.
[Rule definitions](../../Silmaril/Languages/Python/Core/Rules/Defs.lean)

The presentation uses the generic least finite-derivation predicate. The
native interpretations of the three judgment forms are closed under the
schemas. Conversely, induction over the native derivations constructs finite
rule derivations. The resulting equivalences hold for the raw core and
preserve both the label and successor. The Python library uses the
`Semantics` rule API. The downstream fixture combines the public Python
theorems with the `Logic` APIs.
[Correspondence theorems](../../Silmaril/Languages/Python/Core/Rules/Thms.lean)

The fixture constructs an addition derivation from its arithmetic and
expression premises. It transports the return run to the native system
and through a strict rule map that tags each label. It checks the clause
theory under the least model, clause satisfaction under reduct and
naturality of the operational edge interpretation. A marked interpretation
recovers the guarded Python steps, entry and endpoint observations, and UB
marker. Profile guard enforcement occurs at this boundary. The raw rule
presentation works independently of the profile. The regressions include
mixed-sign division, a left-operand exception with a reducible right
operand, and rejection/UB distinct from the defined division error.
[Rule, system and institution fixture](../../tests/languages/python/sos/Regression.lean)

Run the targeted build and regression with the repository toolchain.

```sh
make check CHECK_TARGETS='+Silmaril.Languages.Python.Core.Rules.Thms'
```

This slice covers primitive arithmetic, closed expression evaluation contexts
and body exits. Frames, calls, heap state, host services and maximal-run
transfer are separate proof boundaries.
