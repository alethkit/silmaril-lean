module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Thms

/-! # Disjoint-Store forwarding preserves the word and entire heap -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint

open RVSDG (Locals Origin Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {cells : Nat}
variable {graph rewritten : Graph args} {candidate : Candidate} {certificate : Certificate args}

/-- The concrete check certifies exactly the listed typed address facts. -/
theorem Certificate.check_iff_valid (certificate : Certificate args) (input : Tuple (Val cells) args) :
    certificate.check input = true ↔ certificate.Valid input :=
  Proofs.check_iff_valid certificate input

/-- A matched address wire reads the certificate's observed cell. -/
theorem Certificate.matches_read (certificate : Certificate args) (address : Origin args past .address)
    (matched : certificate.matches address = true) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) :
    readValue address input locals = cell input certificate.observed :=
  Proofs.matches_read address matched input locals

/-- A covered writer targets a distinct cell at every satisfying input. -/
theorem Certificate.covers_read (certificate : Certificate args) (address : Origin args past .address)
    (covered : certificate.covers address = true) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (valid : certificate.Valid input) :
    cell input certificate.observed ≠ readValue address input locals :=
  Proofs.covers_read address covered input locals valid

/-- The exported word supplies the certified cell of the entire exported
heap, including every covered Store. -/
theorem checkExitWith_reads (graph : Graph args) (storeVersion : Nat)
    (accepted : checkExitWith graph storeVersion certificate = true)
    (input : Tuple (Val cells) args) (heap : Heap cells) (valid : certificate.Valid input) :
    let result := graph.denote input heap
    result.2.read (cell input certificate.observed) = result.1 :=
  Proofs.checkExitWith_reads graph storeVersion accepted input heap valid

/-- A rewrite can be reused at each input satisfying its certificate and
at every initial heap for those inputs. -/
theorem rewriteWith_denote (success : rewriteWith graph candidate certificate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) (valid : certificate.Valid input) :
    rewritten.denote input heap = graph.denote input heap :=
  Proofs.rewriteWith_denote success input heap valid

theorem rewrite_denote (input : Tuple (Val cells) args) (heap : Heap cells)
    (success : rewrite graph candidate certificate input = some rewritten) :
    rewritten.denote input heap = graph.denote input heap :=
  Proofs.rewrite_denote input heap success

/-- The checked rewrite preserves and reflects the full explicit-edge
observation at the input used to check its certificate. -/
theorem rewrite_returns_iff (input : Tuple (Val cells) args) (heap : Heap cells)
    (success : rewrite graph candidate certificate input = some rewritten)
    (word : Word) (final : Heap cells) :
    rewritten.Returns input heap word final ↔ graph.Returns input heap word final := by
  rw [rewritten.returns_iff_denote, graph.returns_iff_denote, rewrite_denote input heap success]

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint
