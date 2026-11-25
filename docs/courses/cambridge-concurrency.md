# Shared-store concurrency in Cambridge L1

This development follows the start of chapter 7, pp. 89–91, of Peter
Sewell's *Semantics of Programming Languages*, Cambridge Part IB, dated
12 February 2026. The syllabus on p. 3 names shared-variable interleaving,
simple mutexes, and serializability. The source digest is recorded under
`sewell2026semantics` in the bibliography. [Course notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=89) · [Bibliography](../../references.bib)

```sh
lake build --wfail Silmaril.Courses.Cambridge.Concurrency.Course
```

Import `Silmaril.Courses.Cambridge.Concurrency` for the syntax, typing and
step relation. The `.Course` module adds metatheory and checked examples.

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

## Chapter 7 coverage

| Syllabus item | Notes | Coverage |
| --- | --- | --- |
| Shared-variable interleaving | pp. 89–91 and the process completion observation on p. 97 | Parallel typing and global steps over one store, race derivations, progress, preservation and finite-trace safety |
| Simple mutexes | pp. 92–93 | Follow-up for the mutex-state extension, lock and unlock, and blocking and deadlock examples |
| Thread-local labelled semantics | pp. 94–96, Theorem 27 | Follow-up for labelled transitions and their coincidence with the global rules |
| Ordered two-phase locking and serializability | pp. 93–97, Conjecture 28 | Follow-up for the discipline and its conjectured serializability and deadlock guarantees |
| Chapter exercises | §7.1, p. 97 | Follow-up for Exercises 37–40, including the Unix-like thread extension |

The interleaving relation permits every scheduling choice of an enabled
thread. The safety result concerns finite prefixes of that relation.
