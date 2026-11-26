# Peggy field heap

`Silmaril.SSA.Peggy.FieldHeap` implements a Java-inspired subset of the heap
summary in §8.1. A PEG state token contains one immutable heap snapshot and
the first fault. Field operations consume that token. A write returns a new
token, while a read returns a token and an optional integer. PEG projections
let the next access use the returned token explicitly. The two levels of
partial maps reuse the operational semantics `Environment` and its update
laws. [Profile](../../Silmaril/SSA/Peggy/FieldHeap/Defs.lean) · [§8.1, pp. 58–59](https://arxiv.org/pdf/1012.1802v3#page=58)

A receiver is null or an object identifier. An object is allocated when its
identifier is present in the heap. Its fields are the entries present in its
field map. Field identifiers are resolved opcode parameters. Aliasing depends
on the receiver's object identifier and field, so two different operand slots
can name the same cell. A live access can report a null receiver, an
unallocated object or an absent field. Faults retain the current heap, and
subsequent accesses carry the first fault forward. The profile interprets
field contents as Lean integers and does no arithmetic.

The ordered output ports are `[state, readValue]`. For a completed read,
`ReadResult.ordered` retains the full final heap, fault and optional value.
Each port has Figure 11's outer `Option`. On the read-value port `some none`
is a completed faulting read, whereas `none` is PEG bottom. The field
interpretation is executable on defined arguments. The graph fixture reasons
about the guarded Figure 11 denotation using the checked demand rank and
uniqueness of the node equations. [Guarded semantics](peg-semantics.md)

## Appendix A.1 field rules

Paper locators refer to arXiv:1012.1802v3, PDF SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.

| Paper form | Lean theorem | Premises and observation |
| --- | --- | --- |
| `getfield(setfield(S,O,F,V),O,F) = V` | `getField_setField_value_iff` | The read value is `some V` exactly when the incoming token is live and `O.F` is present. |
| State-preserving form of the same rule | `getField_setField` | On defined operands, forward `V` through the post-store token. A fault suppresses the value and remains observable. |
| `getfield(setfield(S,O,F1,V),O,F2) = getfield(S,O,F2)` | `getField_setField_disjoint` | The write succeeds and the read has a different receiver or field. The read result and first fault agree with reading the original state. The final heap includes the completed write even when the read faults. |
| `setfield(setfield(S,O,F,V1),O,F,V2) = setfield(S,O,F,V2)` | `setField_setField` | On defined operands the last write wins, or the initial fault is preserved. In a PEG, dropping the first value's dependency also needs evidence that doing so preserves strictness. |

The fixture checks aliases, disjoint fields on one object, distinct objects,
overwrite, and fault persistence. A failed disjoint write is a counterexample
to the frame rule without its success premise. The two Figure 11 graphs
prove forwarding equality for their full ordered observations, on successful
inputs and faults. Unconditional forwarding of the proposed value is refuted
at the read port. [Rule statements](../../Silmaril/SSA/Peggy/FieldHeap/Thms.lean) · [Fixture](../../tests/ssa/PeggyFieldHeap.lean) · [Appendix A.1, p. 75](https://arxiv.org/pdf/1012.1802v3#page=75)

The adjacent array rules need indexed cells and bounds checks. The inlining
and collection-summary rules need call and object models. Allocation, class
layout, reference-valued fields, synchronization, Java exceptions and heap
linearization are outside this subset. Programs provide the initial object
and field maps directly.

```sh
lake build --wfail +Silmaril.SSA.Peggy.FieldHeap.Thms PeggyFieldHeapTests PEGCoreTests
lake env leanchecker Silmaril.SSA.Peggy.FieldHeap.Thms
lake env leanchecker tests.ssa.PeggyFieldHeap
```
