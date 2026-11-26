# Discover carried word classes on two native feedback occurrences

`Discovery.discover` enumerates every typed word slot of the existing
`Quads.Loop.Tail.TwoBackedges.Program`. The initial classes group
equal structural keys at the end of the ordered preheader. Each round
seeds the header with the current classes and computes the true and
false feedback keys independently from that completed header. The
next class key consists of the old class and the ordered pair of
feedback keys. Operand order inside each structural key is retained.
The pass materializes each round's labels and feedback keys in finite
tables before it compares or refines them.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Defs.lean) ·
[Native two-feedback checker](sea-of-nodes-gvn-cyclic-feedback-families.md)

The old class in the key prevents merges. Every unstable round splits
at least one class, and the number of classes is bounded by the number
of word slots. The default budget is that slot count. More precisely,
`run_stable_of_fuel` suffices with the slot count minus the starting
class count. The final partition is stable under the same feedback
key computation and refines the initial entry classes.
`normalize_fixed` states stability as equality of the same-class
relation after another round.
[Refinement theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Thms.lean)

Discovery emits one equation for each nonrepresentative slot, using
the first member of its class in register order. The existing
`Family.certify?` checks these equations. The proof shows that entry
and both feedback checks succeed for the discovered family. Passing
the original result slot to `Discovery.certify?` always produces a
native invariant certificate. When proposing another return slot,
admission additionally requires matching post-header keys.
`same_class_at_arrival` proves word equality at any native header
arrival. A checked redirect preserves the actual occurrence and
complete packet and every common-budget result from the original
input bank.
[Family certificate](sea-of-nodes-gvn-cyclic-feedback-families.md)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges (WordSlot)
open GVN.Cyclic.TwoBackedges.Family.Discovery
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (p : Program Opcode regs word) :
    (certify? p p.result).isSome = true :=
  certify?_original_isSome p

example {regs : List (ValueSort Unit)} (p target : Program Opcode regs word)
    (replacement : WordSlot regs) (input : Bank (regs := regs) model)
    (accepted : rewrite? p replacement = some target) (fuel : Nat) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  rewrite_run_eq p accepted fuel input
```

The existing mutually inductive fixture discovers both equations
without nominations and admits the existing return redirect. Reversing
one subtraction on the false feedback edge splits the first pair in
round one. Its dependent pair stays together in that round, then
splits in round two because the header now reads different classes.
The resulting stable partition admits the invariant certificate and
refuses the proposed replacement return.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
make check CHECK_TARGETS="+Silmaril.$topic.Discovery.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Discovery.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click's dissertation §§4.1–4.2 motivates splitting cyclic classes by
the class of each ordered input. This implementation recomputes keys
synchronously on the two actual ordered blocks. It proves stability
from the structural entry seed and soundness through the native family
certificate. Coarseness, semantic completeness, general CFG worklists,
automatic return-slot selection, and producer deletion remain outside
this slice. Click PLDI ’95 §3.1 step 3 motivates the optional checked
return replacement.
[Pinned dissertation](sea-of-nodes-gvn-cyclic.md#sources) ·
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources)
