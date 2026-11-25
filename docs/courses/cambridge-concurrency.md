# Shared-store concurrency in Cambridge L1

This development follows chapter 7, pp. 89–96, of Peter Sewell's
*Semantics of Programming Languages*, Cambridge Part IB, dated 12 February 2026. The syllabus on p. 3 names shared-variable interleaving,
simple mutexes, and serializability. The source digest is recorded under
`sewell2026semantics` in the bibliography. [Course notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=89) · [Bibliography](../../references.bib)

```sh
lake build --wfail Silmaril.Courses.Cambridge.Concurrency.Course
```

Import `Silmaril.Courses.Cambridge.Concurrency` for the first interleaving
language. The `.Course` module adds metatheory, checked examples, and the
mutex extension. For the mutex language and Theorem 27, import
`Silmaril.Courses.Cambridge.Concurrency.Mutex.Course`.

## Rules and checked behavior

`Concurrency.Expr.parallel` extends the L1 expression grammar.
`Concurrency.HasType.thread` views a unit expression as a process, and
`HasType.parallel` composes two processes. The ordinary L1 typing rules
operate over the extended type grammar. For example, sequencing can return
a process on its right-hand side.

`Concurrency.Step.parallelLeft` and `Step.parallelRight` each take one
operand step. Every step sees the same finite store of named integer cells.
Reading a cell and writing an integer each take one step. An expression
such as an increment may take several steps, which can interleave with
the other thread. When all threads finish, the expression is a parallel
tree of `skip` leaves and the configuration is terminal.

The reductions in `Concurrency.Examples` witness both final stores from the
two writes on p. 90. For the p. 91 race that adds 1 and 7 to a cell initially
holding 0, checked schedules reach 1 and 7 when both threads read the initial
value, and 8 when a thread reads the other's write. The derivations identify
concrete finite schedules and their final stores.

| Result | Public name in `Silmaril.Courses.Cambridge.Concurrency` |
| --- | --- |
| Sequential L1 typing and reduction embed | `HasType.ofL1`, `Step.ofL1` |
| Completed processes are terminal | `ProcessDone.terminal` |
| Every typed configuration with a covering store is complete or can step | `progress` |
| Every step preserves its source type and the store domain | `preservation`, `Step.store_domain` |
| Progress holds at every configuration reached by a finite trace | `safety` |

## Primitive mutexes and labelled steps

The mutex extension carries a shared Boolean for each mutex alongside
the finite integer store. In `Mutex.Step`, `lock` checks for `false` and
sets the bit to `true` in a single step. `unlock` sets it to `false` and
can step even when the bit is already `false`. Both commands have type
`unit`.

`Mutex.ThreadStep` describes the expression-side transition and its label.
The five labels distinguish internal computation, a write, a read with a
proposed result, acquisition, and release. `Mutex.Effect` checks the state
premises and applies the action. A local read can propose any integer.
The global configuration rule accepts the proposal when it matches the
current cell. Likewise, a local lock transition can propose an acquisition
when the corresponding global command has to wait.

| Result | Public name under `Silmaril.Courses.Cambridge.Concurrency.Mutex` |
| --- | --- |
| The global and labelled presentations coincide on all configurations (Theorem 27) | `step_iff_labelledStep` |
| Reductions preserve typing and store coverage | `preservation` |
| Interleaving typing and reduction embed | `HasType.ofInterleaving`, `Step.ofInterleaving` |
| A held mutex blocks a global lock step | `lock_terminal` |

The examples check the seven local actions of the guarded increment on p. 95
and the two-lock deadlock on p. 93. The deadlock reaches a terminal
configuration with both acquisitions still pending. The same expression
has type `proc` under the two location declarations.

## Chapter 7 coverage

| Syllabus item | Notes | Coverage |
| --- | --- | --- |
| Shared-variable interleaving | pp. 89–91 and the process completion observation on p. 97 | Parallel typing and global steps over one store, race derivations, progress, preservation and finite-trace safety |
| Simple mutexes | pp. 92–93 | Boolean mutex state, direct rules, typing, blocking and the two-lock deadlock |
| Thread-local labelled semantics | pp. 94–96, Theorem 27 | Labelled expression steps and their state effects, with a proof of coincidence with the global rules |
| Ordered two-phase locking and serializability | pp. 93–97, Conjecture 28 | Follow-up for the discipline and its conjectured serializability and deadlock guarantees |
| Exercise 37 | §7.1, p. 97 | Follow-up for comparison with the Concurrent and Distributed Systems mutex model |
| Exercise 38 | §7.1, p. 97 | Follow-up for necessity examples for the locking-discipline premises |
| Exercise 39 | §7.1, p. 97 | Follow-up for resolving Conjecture 28 |
| Exercise 40 | §7.1, p. 97 | Follow-up for a Unix-like thread extension and communication |

Conjecture 28 asks whether threads following the ordered two-phase
locking discipline are serializable and deadlock-free. The discipline
requires each memory access to be protected by its location's mutex.
On each local trace, acquisition and release alternate per mutex, with
all acquired mutexes released at a terminal state. Acquisitions precede
all releases and follow increasing mutex order. The notes explicitly
allow for a counterexample. The interleaving semantics permits any
enabled scheduling choice.
