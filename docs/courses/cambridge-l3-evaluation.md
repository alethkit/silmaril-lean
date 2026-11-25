# Cambridge L3 type checking and evaluation

Import `Silmaril.Courses.Cambridge.L3.Evaluation` for the Exercise 31
workflow. The checker follows the collected expression and store judgments
in the 12 February 2026 Cambridge notes. The workflow uses the existing
`Concrete.parseResolved` byte parser. The syntax guide also describes the
parser with separate spelling classes.
[Exercise 31 and §5.5](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=82) ·
[Concrete syntax](cambridge-l3-concrete.md)

`infer Θ Γ e` computes the type of any resolved core term using the supplied
location and variable types. It compares annotations structurally, retaining
record label order. `infer_iff_hasType` proves soundness and completeness
against `HasType` for every supplied environment and expression, including
runtime location literals and open expressions. `checkStore Θ s` checks
that the location environment and store have the same domain and that
every stored value has its declared type in the empty variable environment.
`checkStore_eq_true_iff` gives exact agreement with `StoreTyped`. The typing
of a nonempty store is supplied by the caller, so validation can use types
of cells reached through cycles.

`evaluate bytes Θ s fuel` checks the parsed expression in the empty
variable environment. Start with `∅` for both `Θ` and `s` to run a program
that allocates its own cells.

| Result | Meaning |
| --- | --- |
| `parseError` | The byte parser rejected the input. |
| `storeTypeError` | Parsing succeeded and the supplied store typing failed validation. |
| `expressionTypeError` | Parsing and store validation succeeded and the closed expression has no core L3 type. |
| `evaluated T (.returned v s')` | A value returned with the inferred type and its final store. |
| `evaluated T (.outOfFuel c)` | The run consumed the entire transition budget and `c` still has a next step. |
| `evaluated T (.stuck c)` | The raw runner can report a stuck configuration. `evaluate_ne_stuck` rules out this result for the checked workflow. |

`runFuel_spec` records the number of selected transitions and the stopping
condition. A value already present at the start returns with zero fuel.
`evaluate_returned` proves that a return is reachable along a selected trace
within budget and preserves the inferred type under an extension of the
location typing for the final store. Every selected transition satisfies
the original `Step` rules. `evaluate_of_selectedSteps` proves the converse
for a selected trace ending at a value within budget.

The reducer chooses one fresh address according to its existing policy.
Completeness of the runner refers to that policy's traces. The original
relation may also return at other addresses. Fuel exhaustion records a
finite prefix with a possible next step. The workflow provides finite
evaluation results and makes no termination claim.

[Checker](../../Silmaril/Courses/Cambridge/L3/TypeChecker.lean) ·
[Workflow and proofs](../../Silmaril/Courses/Cambridge/L3/Evaluation.lean) ·
[Executable examples](../../Silmaril/Courses/Cambridge/L3/Evaluation/Examples.lean)
