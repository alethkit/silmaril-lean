module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Correctness

/-! # Checked load forwarding preserves the word and final heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding

open RVSDG (Locals Origin Port Tuple)

variable {args : List ValueSort} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate}

/-- An accepted exit check ties the exported scalar to the addressed cell
of that exact exported memory version. -/
theorem checkExit_reads (graph : Graph args) (address : Port args .address) (storeVersion : Nat)
    (accepted : checkExit graph address storeVersion = true)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    let result := graph.denote input heap
    result.2.read (input.get address) = result.1 :=
  Proofs.checkExit_reads graph address storeVersion accepted input heap

/-- Redirect all users of a total Load when the replacement wire supplies
the exact read value at the current heap. -/
theorem replaceLoad_denote {past : List (List ValueSort)} {version : Nat}
    (memory : MemoryInput version) (address : Origin args past .address)
    (rest : Body args ([.word] :: past) version) (value : Origin args past .word)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (agrees : heap.read (readValue address input locals) = readValue value input locals) :
    (rewire rest (dropLoad value)).denote input locals heap =
      (Body.load memory address rest).denote input locals heap :=
  Proofs.replaceLoad_denote memory address rest value input locals heap agrees

/-- The rewritten graph has the same complete denotation for every input. -/
theorem rewrite_denote (success : rewrite graph candidate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  Proofs.rewrite_denote success input heap

/-- Accepted forwarding preserves and reflects the source snapshot observation. -/
theorem rewrite_returns_iff (success : rewrite graph candidate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) (word : Word) (final : Heap cells) :
    rewritten.Returns input heap word final ↔ graph.Returns input heap word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote success]

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding
