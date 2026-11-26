# Reuse a checked entry add in a materialized diamond

`Materialize.EntryReuse.rewrite?` takes the actual right-materialized
program and one typed producer nomination in its common entry table.
It checks the emitted suffix for literal `k`, inner `capture + phi`,
and return of `inner + k`. The nomination must have the existing typed add
key with the original capture argument on the left. On the right
it must have a shared word that the original Φ forwards in both
actual predecessor occurrences. The check compares addresses after
lifting the shared wire into each arm's full scope. A branch-local
producer cannot serve as the entry nomination. `rewriteAt?` resolves
a numbered nomination only in the shared table.
[Checker and emitter](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Defs.lean)

The emitted graph forwards the entry result in a new first join
column and keeps the original Φ operands in the second column. The
shared table, original capture, predicate, arms and Region order
are carried through. The suffix retains its literal and the existing
outer add, whose left operand is now the forwarded entry result.
The old inner result routes to that boundary value and the outer
result shifts down one binding.

`check_provenance` proves exact ordered key and occurrence-wire
identity. `emit_agrees` and `emit_packet_eq` preserve every routed
read and all values of a supplied outgoing packet, including
additional reads of the original Φ or the elided inner result.
`rewrite?_returns_iff` compares the emitted program with the
materialized intermediate. `materialize_then_reuse_returns_iff`
compares it with the original two-Φ program for every typed input.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Thms.lean)

Cliff Click's *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1 step 3, provides the exact-key replacement and removal precedent.
Here availability comes from the common entry table of the native
diamond, and the existing `Producer.read_key` law supplies the
ordered add semantics. This slice checks one nominated shared add
and one emitted suffix shape. General dominance queries, code motion,
extra equivalences and iterative GVN are outside the profile.
[PLDI ’95](https://doi.org/10.1145/207110.207154) ·
[Paper pin and acyclic GVN proof](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse (rewriteAt?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.RVSDG (Tuple)

def sample : AddPhi.Pair.Source [.predicate, word, word] [[wordPort], [wordPort]] where
  shared := .cons (.literal 7) .nil
    (.cons .add (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail .head)) .nil)) .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms := fun _ => {
    sigs := [], dataflow := .nil
    outputs := .cons (.arg (.tail .head)) (.cons (.output (0 : Fin 2) .head) .nil) }

def run (guard : Bool) : Except Refusal (Option (Nat × BitVec 64)) :=
  (rewrite sample (.tail (.tail .head)) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let target ← rewriteAt? emitted (.output 1 0)
    let entry : Tuple (Val model.value) (dataPorts [.predicate, word, word]) :=
      .cons ⟨guard⟩ (.cons (3 : BitVec 64) (.cons (0xffffffffffffffff : BitVec 64) .nil))
    pure (target.suffix.sigs.length, target.denote entry)

#eval (run false, run true)

example : (run false, run true) = (.ok (some (2, 9)), .ok (some (2, 9))) := rfl
```

The regression additionally uses unequal arm scopes and checks a
three-field outgoing packet. It refuses a same-shaped add available
only on the second arm and a Φ that reads a different input on that
occurrence.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/EntryReuse/Regression.lean)

```sh
topic=SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
make check CHECK_TARGETS="+Silmaril.$topic.Thms +Silmaril.Proofs.$topic.Regression"
```
