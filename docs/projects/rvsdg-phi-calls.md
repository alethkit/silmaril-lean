# RVSDG φ linking and finite recursive calls

The φ implementation follows Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers*,
arXiv:1912.05036v2, §4.2.3 and Definitions 7–8 for φ, and §4.3 for θ. The versioned PDF has
SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The ω linker reads typed imports and produces the ordered export tuple.
It links λ closures and δ initializers as before. At φ, it reads the
outer context once and packages the static member table with the context.
Each output contains that group environment and a typed member index.
The stored environment does not contain its own member references.
Invocation reconstructs the region's recursion arguments and its
in-scope earlier physical λ outputs as references to the same group.
It then reads the selected λ's captures and enters the body with the
ordinary argument tuple. Module linking traverses the same typed graph
or term interfaces used for λ, δ, φ and ω. `link_toGraph` proves exact
agreement on exports, including member references and numbered global
identities.
[Runtime definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Defs.lean) ·
[Recursive linker](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Defs.lean)

The inductive `Returns` judgment has explicit premises for entering a
callable, running its body, applying a callable, entering the chosen γ
arm, and completing θ iterations. A stopping body publishes the carried
tuple. A continuing body feeds that tuple to a fresh activation with
an empty local prefix. Both body execution and recursive calls use the
same judgment. Its rules are independent of the bounded evaluator.
`call_iff` proves that a call returns an exact typed value/state tuple
iff some pair of call-depth and per-θ bounds returns it.
`returns_eventually` supplies sufficient bounds valid at every larger
pair. During a single θ invocation the remaining iteration count
decreases, while its body and callees still receive the full per-θ
budget. Exhaustion at a particular bound leaves divergence undecided.
The linker takes a supplied import tuple. External import cycles and
linking by symbol name are outside this slice.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Thms.lean)

The first fixture links two mutually recursive members. The first
captures the second through a recursion argument, and the second
captures the first through its earlier physical λ output. Both capture
an imported value, pass a decreasing state through alternating calls,
and return the captured value and final state at zero. A second linked
φ member enters θ and calls itself inside the selected γ arm of the
body. The fixture checks exhaustion independently at each bound and
the exact returned tuple when both bounds suffice.
[Fixtures](../../tests/ssa/RVSDGPhiCalls.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPhiCalls.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```

## Typed continuations for non-tail calls

The continuation machine steps the existing runtime jobs and the actual
body of each resolved closure or φ member. At a binding, the stack saves
the typed remainder of the region, its entry tuple, and its current
locals. The node reads its operands in that scope. An application opens
the callee with fresh locals, and γ enters only its selected child. When
the result arrives, the machine appends the entire typed tuple to the
saved locals before running the remainder. The caller's earlier wires
and the callee's returned ports can both feed later nodes. A θ loop
frame keeps this enclosing continuation. Each body starts with empty
locals and takes the carried tuple as its input. Selector `1` feeds
back the carried ports to a fresh body activation. Selector `0` returns
those ports to the enclosing binding, which resumes the saved suffix.
[Machine definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Defs.lean)

At each step the proof invariant interprets the active job and each
pending frame with the independent `Returns` judgment. Induction on
`Returns` constructs a completed trace, using both the stopping and
continuing θ rules. The theorem `completes_iff_returns` gives both
directions for all existing jobs, including θ. The real bounded
evaluator agrees on the same full tuple through `Recursive.call_iff`.
The theorem concerns finite returns.
[Adequacy API](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Thms.lean)

The linked φ regression descends twice before a base call. An exact
intermediate configuration contains both non-tail application frames,
including the saved state before each callee runs. The prefixes append
`1` to state, the base appends `2`, and each suffix appends `3` and the
length of its own saved prefix state. The final tuple is data `12` and
state `[1, 1, 2, 3, 2, 3, 1]`. Both the stack machine and the existing
bounded evaluator return it.

A second module links a λ that captures the φ member and calls it from
inside θ. The fixture checks that the second body starts with empty
locals and the fed-back tuple. It then checks that exit returns the
carried tuple to the same parent continuation. The final state
`[1, 4, 2, 5, 4, 2, 6, 3, 1]` records the parent prefix, both body and
callee activations, feedback, exit, and the resumed suffix. The
bounded evaluator agrees and exhausts with only one allowed iteration.
[Continuation fixture](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveContinuations.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Thms'
```

## Productive θ feedback

A feedback iteration consists of a finite `Returns` derivation for
the actual body and a selector requesting feedback. The derivation
starts with the full carried tuple and empty locals and supplies the
entire next carried tuple. A productive feedback run repeats these
completed iterations indefinitely.

`returns_iff_delimited` relates a finite job derivation to continuation
microsteps up to its first return to the supplied frame. The proof
attaches or removes the same outer stack on both sides of each local
step, so nested calls and loops keep their ordinary transitions.
`iteration_iff_segment` then matches one feedback iteration to
the actual body followed by its feedback edge.
[Definitions and finite correspondence](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Feedback/Thms.lean)

The stream theorem places every supplied carried tuple at a
successive restart of one actual continuation trace, with the same
saved parent. In reverse, supplied restart and body-return positions
and the first-return guard recover each finite body derivation. This
statement is about completed feedback iterations. A body that supplies
no finite return, whether it runs indefinitely or stops without
returning, supplies no feedback segment. The typed continuation
machine already rules out incomplete terminal states.

The linked regression adds an always-feedback variant of the θ body.
Each activation calls the linked φ member to completion and adds
`[4, 2, 5]` to state. Microsteps `6`, `30`, and `54` check the initial
iteration and the next two restarts with distinct full carried tuples
and the original parent frame. The fixture gives a finite derivation
for every iteration and exercises both directions of the stream proof.
[Linked fixture](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Thms'
```

## Infinite execution within a θ activation

`stays_iff_decomposes` takes an actual infinite continuation trace
starting at a θ restart. `body_decomposes` also accepts a stream
already at the freshly entered body. It prepends the actual entry
microstep so both statements use the same checkpoint convention.
The scope guard requires selector `1` at every return to the specific
saved loop frame. A finite exit followed by infinite parent execution
fails this guard. Nested frames still take their ordinary steps.

The extraction searches for the first return after each restart.
Determinism fixes the following restart and its entire carried
tuple. The result gives either unbounded first-return checkpoints
on the supplied trace or a finite sequence of such intervals ending
in a delimited infinite body suffix. The alternatives are disjoint.
Each completed interval recovers the independent finite body
derivation via `Interval.iteration`. Conversely, either decomposition
ensures that every return to the saved frame takes feedback.
`trace_of_iterations_then_body` also builds a scoped machine stream
from any finite sequence of feedback derivations and an infinite
delimited body stream. Both branches require a genuine microstep
at every index.
[Theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Feedback/Divergence/Thms.lean)

The regression keeps the linked productive feedback example and
extracts its checkpoints from the microsteps. A second linked driver
enters a body whose φ member calls itself with a pending non-tail
suffix. At step 24 the machine has two such suffixes waiting and
the argument state is `[1, 4, 1, 1]`. The proof uses typed machine
progress and finite adequacy to construct an infinite body stream
with zero completed feedback iterations.
[Linked fixtures](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Feedback.Divergence.Thms'
```

## Productive descent through non-tail calls

`Descent.Prefix` is an independent judgment over the real opened body
of a call. It uses finite `Returns` derivations for completed bindings,
follows the selected γ arm, and stops at a designated application with
its full callable and argument tuple. The saved suffixes retain their
entry arguments and the preceding local tuples. The callee's result
interface may differ from the caller's.

`Run.checkpoints` realizes a sequence of these prefixes as successive
entry checkpoints in one actual continuation stream. Each checkpoint
keeps the exact stack obtained by pushing the newly pending bindings on
the previous stack. `Run.stack_grows` proves that each opened caller
contributes at least one saved frame. Earlier completed jobs can use
calls and θ. The selected path can go through ordinary bindings,
selected γ arms, and θ bodies that are still active.

Under θ, the prefix records a finite sequence of completed feedback
iterations, including the empty sequence. Each iteration uses a
finite `Returns` derivation and its feedback selector. The full
carried tuple feeds the next fresh body. The selected call leaves
the θ frame in its original position among the pending bindings.

`entry_of_theta_interval` recovers a prefix and its exact saved stack
from two entries on an actual continuation stream. The caller must
remain live and each intervening call must return to its own stack
before the selected entry. The proof uses the first return of each
completed binding or θ body to recover its independent derivation and
the observed feedback. A θ activation may still be open at the selected
call. The existing `entry_of_interval` statement keeps its stronger
premise that intervening θ activations have also returned. These
results concern unbounded call nesting after finite feedback in each
prefix. Infinite sequences of completed θ feedback use the separate
feedback theorems.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Defs.lean) ·
[Proof statements](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Thms.lean)

The ω fixture links a φ group with a returning helper and two mutually
recursive members. Each prefix calls the helper to completion, updates
the helper's value and state, then calls the other member before running
a nonempty suffix. At microstep 28 the active callable is the first
member again, with data `32`, state `[1, 10, 1, 20]`, and both distinct
suffixes pending with their own saved locals.

A second linked φ fixture starts each activation with a θ body that
feeds back once, appending `7` to the state. The restarted body adds
`8` before it enters a non-tail recursive call in the selected γ arm.
The regression checks fresh locals after restart and the ordered
stack at step 42. It contains both θ frames and six saved binding
frames, with argument state `[7, 8, 7, 8]`. The fixture also checks
the empty feedback prefix and reflects the first active-θ call interval.
[Linked fixture](../../tests/ssa/RVSDGRecursiveDescent.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveDescent.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Thms'
```

## Extracting the first live child or productive feedback

`split_live` starts at a real call on a supplied infinite continuation
stream. The call's saved frame must remain live, meaning that the stream
never reaches a return to that exact frame. The theorem derives the
checkpoints from the stream using a classical split on liveness.
It applies to linked φ members and to
ordinary linked closures. For a call started at the empty stack,
`split_start` derives root liveness from the infinite steps.

When a later call never returns to its own stack, the first such
entry is selected. A typed stack delimiter shows that each earlier
returning call must finish before the selected entry. Guarded reflection
then yields the independent prefix, with its exact typed arguments and
saved frames. The prefix includes any finite θ feedback on the way
to the selected application. The selected stack has strictly more
frames, and its liveness and actual entry position permit another
application of the theorem on the same stream.

If every later call returns, induction on finite region syntax uses
the actual node returns and selected γ arms to locate a live θ. A
live θ either yields unbounded completed feedback or reaches a
particular body activation that stays live. In the latter case the
proof continues inside that finite body syntax. The feedback result
gives actual restart positions and finite body derivations on the
original stream's suffix.

The proof uses the current deterministic machine. Each primitive is
a total typed tuple transformation that returns in one microstep,
with state threaded through its ports. γ takes a single selected child,
and linked calls resolve through the total typed resolver. Infinite
streams must take an actual step at every index. Primitive failure,
nondeterministic scheduling and finite stuck execution are outside
this classification.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Completeness/Thms.lean)

The linked regressions supply raw streams with no call or restart
checkpoints. One invokes a φ export that repeatedly makes a non-tail
recursive call with a pending suffix. The other invokes a φ export
with an always-feedback θ and no deeper call.
[Linked fixtures](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveContinuations.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Thms'
```

## Classification from a linked root

`classify_linked` starts with the typed callable at an ω export, its
arguments, the empty stack, and the actual infinite microsteps. A
return to the empty stack has no following transition, so the trace
itself gives the initial live delimiter. The assumptions on total
single-step primitives and deterministic transitions are the same as
for `split_live`.

Each nested child continues at the least live call found by
`first_child`. It retains the independent finite prefix, including
finite θ feedback, and the exact typed stack at that position. A
nonempty finite chain strictly increases both the microstep index
and the saved stack depth. The global proof classically splits on
whether a finite such chain ends at productive feedback. When it
does, the final call and θ restart indices are on the supplied
stream. Otherwise coinduction chooses an endless chain of successive
least-child witnesses. `chain_checkpoints` chooses the independent
prefix witnesses to recover a single `Descent.Run` at those same
positions.

`calls_sound` runs the independent infinite-call certificate through
the existing simulation. The finite-call branch observes the route
from its final call to θ on the supplied trace. The independent
reaching judgment below reflects that route and replays it.
[Root theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/Completeness/Global/Thms.lean)

The linked fixture starts at an exported λ that calls a φ member
and leaves its suffix pending. The classifier extracts a nonempty
finite chain ending at the φ call at microstep 3 and finds
productive θ feedback inside it. The trace supplies no chain
or restart checkpoints.
[Linked fixture](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.Completeness.Global.Thms'
```

## Independent certificates for productive feedback

`ThetaReach.Reaches` describes a finite route to a selected θ restart
without a machine trace. A completed binding uses independent
`Returns`, including when the binding evaluates an application. A
selected γ arm receives its actual typed input. Entering a live θ body
after finite feedback records the exact carried tuple, fresh locals
and saved loop frame. The route can also choose a later restart of
the same θ. The pending bindings and loop frames preserve their
original order and port types.

`reaches_of_interval` recovers the route to the exact observed restart
and stack. It delimits the first return of every completed binding and
θ body. In the finite branch of the rooted classifier, all intermediate
calls return before the selected restart, because that restart's parent
frame stays live. `feedback_of_observation` then projects a finite chain
of the existing call prefixes followed by the independent θ route and
productive feedback.

`linked_iff` relates actual infinite continuation execution at a typed
ω export to either of two independent certificates. One is the
existing infinite call descent. The other uses the finite chain and
θ route to replay up to a selected restart, then stitches the
productive feedback steps. Completeness uses the classical rooted
classifier. The equivalence applies to the deterministic machine
with total single-step primitives and explicit state ports.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/Descent/ThetaReach/Thms.lean)

The linked relay fixture constructs its certificate from the syntax
and finite return rules. The exported λ calls the φ member, which
completes one feedback body before the selected restart. The fixture
runs the certificate through the forward implication and uses the
original raw relay execution to exercise the reverse implication.
A second finite route checks a carried state of `[1, 4, 2, 5]`
after a completed feedback iteration with a linked return.
[Linked fixture](../../tests/ssa/RVSDGRecursiveContinuations.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Descent.ThetaReach.Thms'
```
