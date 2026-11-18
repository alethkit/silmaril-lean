# A typed user/kernel boundary

[`Silmaril.Process.TypedSyscall`](../../Silmaril/Process/TypedSyscall/Defs.lean)
is a small POSIX-style process model, not a POSIX or Linux conformance claim.
It describes one selected user step or completed kernel call, without
committing to syscall numbers, an ISA, or a memory representation.

| Plug | Supplied by the caller | Checked filling |
| --- | --- | --- |
| CPU / ABI boundary | `Cpu` consumes an image, core and store; it retires, stops, or yields a typed call with a reply continuation. Registers, trap semantics and syscall-number conversion are outside the interface. | A two-stage client that writes a buffer and then exits; not an x86 runner. |
| Image | Immutable input to the CPU; mapping and ownership constraints are stated by the image/client. | Buffer address and count. No ELF loading. |
| Memory and kernel environment | `Store` is carried explicitly through CPU and kernel transitions. A filling can pair memory with descriptor or other service state; a store frame is a property of that filling. | Existing `Syscall.State`: permissioned byte memory, descriptors and exit state. |
| Parallelism/scheduling | `Scheduler` selects a core and how to replace its slot in the pool. A `none` selection is idle, not a verdict on completion or deadlock. | A singleton pool and an idle-policy check. No thread creation, blocked-call scheduling, fairness or weak-memory semantics is implemented. |

A `Signature` assigns a type `Response req` to each request. `Signature.Hom`
maps requests forward and projects responses **back at that request's index**.
`Action.push` and `Kernel.pull` compose (`Action.push_then`, `Kernel.pull_then`).
[`step_push_iff`](../../Silmaril/Process/TypedSyscall/Thms.lean) proves that
pushing the CPU or pulling the kernel gives the same observations and outcomes,
including store changes and exit without resumption. Its kernel is the
*constructed* pullback, not an arbitrary kernel with a similar signature. To
reuse a theorem on an independent kernel, prove the appropriate reply/exit,
state and observation correspondence and separately establish progress. The
transport neither supplies a return for every call nor turns an absence of
completion into a fault. Precise fault state or resumable traps would require
a richer CPU stop outcome; they are not hidden in the syscall reply type.

The [checked filling](../../Silmaril/Process/TypedSyscall/Checks.lean) maps a
client send request to `write` on descriptor 1 in the existing
[`Syscall.Step`](../../Silmaril/Process/Syscall.lean) relation. The client sees
`Option Nat` rather than a raw result: the continuation loses errno, but the
kernel event is retained. `exit` has response `Empty` and uses a separate
completion constructor. The checks cover a one-byte write and subsequent exit,
plus a bad-descriptor return observed as failure by the client.

```sh
lake build --wfail Silmaril.Process.TypedSyscall.Checks
```

The next useful filling is one existing CLI-loaded client. Keep the loader's
image predicate and concrete ABI unchanged, and prove that the new boundary
agrees on its emitted requests, replies, store effects and stops before moving a
caller. LPS's numbering, lazy mappings and access traces need a separate adapter.
This does not introduce a decoder API or replace existing process models.
