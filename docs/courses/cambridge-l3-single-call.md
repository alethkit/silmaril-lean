# Cambridge L3 stored closure adequacy

Import `Silmaril.Courses.Cambridge.L3.Denotation.SingleCall` for the model and
adequacy theorems, also exported by `L3.Course`. The checked example is in
`SingleCall.Examples`. The rules are from §5.5 of Sewell's 12 February 2026 Cambridge notes, pinned as
`sewell2026semantics`. [Pinned notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=78)

## Model and exact scope

The `Admitted` predicate covers a lexical expression or one tail application
after zero or more strict lets. The bound expressions and the call operands
use the lexical fragment. Each lambda returned by the function operand must
have a body in that fragment. For a prefix let, the criterion applies to the
continuation in the environment and store of every possible binding return.

The interpretation uses the existing `StateT Store SetM` computations.
A strict let binds the result of its initializer. Application binds the
denotations of the function and argument in that order. The function value
carries a quoted lambda whose body already contains its captured lexical
values. The body runs with the new argument in slot zero and the current
store left by argument evaluation. Allocation branches over the fresh
addresses in that store. All the evaluation clauses compose denotations.

`adequateWith` proves that a denotational result and final store are exactly
a finite return of the original direct rules from the source instantiated
by the environment. The proof splits returning traces at the strict let and
call rules. In the application case it reconstructs function evaluation,
argument evaluation and the beta instance, using the lexical adequacy
theorem for all three. `adequate` specializes to an empty environment.
`typed_return` preserves typing and extends the location typing for each
possible returned store.

The theorem concerns finite may returns in this single-call fragment.
Nested applications, recursive-function declarations, and executing arbitrary
functions read from general references require a broader model and proof.

## Checked example

The example binds 7, allocates a cell containing a lambda that captures that
number, dereferences the cell, and calls it. The argument writes 9 to location
0 and returns 1. The body reads location 0 and returns 17. For an initial
store that already allocates location 0, `program_steps_iff` characterizes
the entire set of finite returns. Every fresh address can hold the function
cell, the argument's write persists, and the returned integer is 17.
With an initial value of 3 at location 0, the example checks two distinct
allocation stores and rules out the stale-store result 11.
[Model and adequacy](../../Silmaril/Courses/Cambridge/L3/Denotation/SingleCall.lean) ·
[Checked example](../../Silmaril/Courses/Cambridge/L3/Denotation/SingleCall/Examples.lean)
