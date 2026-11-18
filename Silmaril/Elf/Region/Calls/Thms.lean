module

public import Silmaril.Elf.Region.Calls.Defs
public import Silmaril.Semantics.Function.Thms
import Silmaril.Proofs.Elf.Region.FunctionCalls

@[expose] public section
namespace Silmaril.Elf.Region.Calls
open Silmaril.Semantics.Function
open Silmaril.Machine.Region (BinaryObject)

theorem readable_rows (source : BinaryObject) (plan : Plan) :
    ReadableRows source plan (rows (extract source plan)) := Proofs.readable_rows source plan

theorem decomposition_problem (source : BinaryObject) (plan : Plan) :
    DecomposeProblem (ReadableRows source plan) source (asModel source (extract source plan)) :=
  fun name body candidate => readable_rows source plan name body candidate.2

theorem finding_evidence {source : BinaryObject} {plan : Plan} {row : Row} {finding : Finding}
    (member : row ∈ extract source plan) (available : row.available = true) (found : finding ∈ row.findings) :
    FindingAt source plan finding := Proofs.finding_evidence member available found

theorem mem_directArcs {inventory : Inventory} {source : Nat} {dest : Node signature} :
    (source, dest) ∈ directArcs inventory ↔ DirectEdge inventory (.localFn source) dest :=
  Proofs.mem_directArcs

theorem reach_sound {inventory : Inventory} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ reach inventory entry rounds) :
    Reachable (directGraph (analysis inventory).may) (.localFn entry) dest :=
  Proofs.iterate_sound (fun _ h => (List.mem_singleton.mp h).symm ▸ Relation.ReflTransGen.refl)
    (fun _ _ path edge => Relation.ReflTransGen.tail path edge) mem

theorem nonemptyReach_sound {inventory : Inventory} {entry rounds : Nat} {dest : Node signature}
    (mem : dest ∈ nonemptyReach inventory entry rounds) :
    CallPath (directGraph (analysis inventory).may) (.localFn entry) dest :=
  Proofs.iterate_sound (fun _ h => Relation.TransGen.single (Proofs.successor_iff.mp h))
    (fun _ _ path edge => Relation.TransGen.tail path edge) mem

theorem reach_exact {inventory : Inventory} {entry rounds : Nat}
    (fixed : expand inventory (reach inventory entry rounds) = reach inventory entry rounds) :
    ReachProblem (directGraph (analysis inventory).may) (.localFn entry)
      {dest | dest ∈ reach inventory entry rounds} :=
  reach_problem_of_certificate ⟨Proofs.root_mem inventory entry rounds,
    fun {_ _} h edge => Proofs.step_closed fixed h edge, fun {_} mem => reach_sound mem⟩

end Silmaril.Elf.Region.Calls
