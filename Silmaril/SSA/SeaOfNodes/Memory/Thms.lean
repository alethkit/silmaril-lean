module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Correctness

/-! # The memory-edge and current-heap interpretations agree -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory

open RVSDG (Locals Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}

/-- Reading exactly the addressed cell gives the stored word. -/
theorem Heap.read_write_same (heap : Heap cells) (address : Address cells) (value : Word) :
    (heap.write address value).read address = value :=
  Function.update_self (β := fun _ : Address cells => Word) address value heap

/-- A store preserves the contents of a distinct cell. -/
theorem Heap.read_write_other (heap : Heap cells) (written observed : Address cells)
    (value : Word) (distinct : observed ≠ written) :
    (heap.write written value).read observed = heap.read observed :=
  Function.update_of_ne (β := fun _ : Address cells => Word) distinct value heap

/-- Resolving explicit memory wires agrees with threading the current heap.
The agreement includes the final heap, even if the scalar ignores a Store. -/
theorem Body.exec_iff_denote (body : Body args past version) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (states : Snapshots cells version)
    (value : Word) (final : Heap cells) :
    body.Exec input locals states value final ↔
      body.denote input locals (states (Fin.last version)) = (value, final) :=
  Proofs.exec_iff_denote

/-- From Start, the source rules and the denotation return exactly the same observation. -/
theorem Graph.returns_iff_denote (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Heap cells) (value : Word) (final : Heap cells) :
    graph.Returns input initial value final ↔ graph.denote input initial = (value, final) :=
  graph.exec_iff_denote input PUnit.unit (fun _ => initial) value final

end Silmaril.SSA.SeaOfNodes.Memory
