# Cambridge L3 stored closures and call depth

Import `Silmaril.Courses.Cambridge.L3.Denotation.CallDepth` for the nested
and let-bound call model and adequacy theorems. `L3.Course` exports it and the original
`SingleCall` interface. The rules are from §5.5 of Sewell's 12 February
2026 Cambridge notes, pinned as `sewell2026semantics`. [Pinned notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=78)

## Single call

The `SingleCall.Admitted` predicate covers a lexical expression or one tail application
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

The original interpretation is the depth-one case. Its admission predicate
keeps its original premises. `SingleCall.Admitted.toCallDepth` supplies the
corresponding depth-one admission. Proofs that explicitly unfold the
interpreter can use `CallDepth.denoteWith` and `CallDepth.denoteLayer`.

### Checked example

The `SingleCall.Examples` program binds 7, allocates a cell containing a
lambda that captures it, dereferences the cell, and calls the function.
The argument writes 9 to location
0 and returns 1. The body reads location 0 and returns 17. For an initial
store that already allocates location 0, `program_steps_iff` characterizes
the entire set of finite returns. Every fresh address can hold the function
cell, the argument's write persists, and the returned integer is 17.
With an initial value of 3 at location 0, the example checks two distinct
allocation stores and rules out the stale-store result 11.
[Model and adequacy](../../Silmaril/Courses/Cambridge/L3/Denotation/SingleCall.lean) ·
[Checked example](../../Silmaril/Courses/Cambridge/L3/Denotation/SingleCall/Examples.lean)

## Nested calls

`CallDepth.denoteWith 0` is the lexical model. In the default
`.tail` mode at depth `d + 1`, a tail application may follow strict lets. The let initializers and the
function and argument operands remain lexical. Application invokes the
quoted lambda body at depth `d`, with the argument in slot zero and
the store left by the argument. Each invoked body can have its own
lexical lets and tail call.

`CallDepth.Admitted` checks each let continuation after every possible
initializer return and each callee after every pair of function and
argument returns, in the resulting environment and store. The index
bounds successive invocations through selected bodies. Lexical
computations can have traces of arbitrary length. The denotation
composes `StateT Store SetM` operations and retains every permitted
fresh allocation. The proof of `adequateWith` factors returning
source traces at let and application and uses the lower-layer
correspondence when entering a callee. `adequate` specializes to an
empty lexical environment. `typed_return` gives the result type and
a compatible typing of each final store.

### Checked example

`CallDepth.Examples.program` binds an `int → int` helper, then
allocates an `int → int` closure that captures it. The program
dereferences and calls the outer closure on 3. That closure calls the
captured helper on 4. The helper allocates a cell containing 4 and reads
it back. `program_steps_iff` shows that every pair of distinct addresses
outside the initial store gives a return of 4 with the two insertions,
and that these are all finite returns. The depth-one denotation has no
return for this program. The regressions realize two different address
choices and check result and store typing.

[Call-depth model and adequacy](../../Silmaril/Courses/Cambridge/L3/Denotation/CallDepth.lean) ·
[Nested example](../../Silmaril/Courses/Cambridge/L3/Denotation/CallDepth/Examples.lean)

## Let-bound calls

Use `.sequenced` in `CallDepth.denote`, `denoteWith`, and `Admitted`
to allow calls in strict let initializers. The initializer and its
continuation both run at the same positive depth. Structural recursion
handles the two let subterms, and entering a callee still lowers the
depth. `Admitted.letBound` requires admission of the initializer and
of the continuation for every returned value and intermediate store.
`adequateWith` and `adequate` use the same direct-rule let and call
factorizations for both modes. They retain the complete result and
final store. The original tail mode remains the default.

The checked program binds the reference returned by a call allocating
an integer cell with contents 4. The continuation assigns 5 through
that reference and reads it back. `program_steps_iff` proves that the
result is 5 and the exact final store is the initial store extended by
that cell with contents 5, for every fresh address. `program_typed`
and the typed-return regression check the result and store typing.
`program_not_admitted_tail` rules out admission in the tail mode at
every depth. [Let-bound example](../../Silmaril/Courses/Cambridge/L3/Denotation/CallDepth/LetBoundExample.lean)

The theorem applies to admitted terms at the chosen depth. The new
call position is the initializer of a strict let. Application operands
and the expressions handled directly by the lexical model remain in
the lexical fragment. Recursive-function declarations and unrestricted
call chains through general references are outside this scope. The
observation is finite may return with a concrete final store.
