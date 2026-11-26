module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.Correctness

/-! # Certification of backedge discovery, header union and loop depth -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopForest

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open NaturalLoop (Backedge Member)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {tree : DominatorTree cfg} {blocks : List (Target Label)}

/-- Every reported slot is a reachable CFG edge whose target dominates its source. -/
theorem discover_sound {edges : List (Backedge Label)}
    (result : discover? tree blocks = some edges) {edge : Backedge Label}
    (member : edge ∈ edges) : ActualBackedge cfg edge :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.discover_sound result member

/-- With complete dominator evidence, discovery returns every reachable
dominating successor occurrence, including parallel edges. -/
theorem mem_discover_iff {edges : List (Backedge Label)}
    (result : discover? tree blocks = some edges) (complete : tree.Complete)
    (edge : Backedge Label) : edge ∈ edges ↔ ActualBackedge cfg edge :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.mem_discover_iff result complete edge

/-- Coalescing returns one record per discovered header. -/
theorem loopHeaders_nodup {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) : (loops.map HeaderLoop.header).Nodup :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.loopHeaders_nodup result

/-- With complete evidence, the header keys are exactly the targets of actual backedges. -/
theorem mem_loopHeaders_iff {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) (complete : tree.Complete)
    (header : Target Label) : header ∈ loops.map HeaderLoop.header ↔
      ∃ edge, ActualBackedge cfg edge ∧ edge.header = header :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.mem_loopHeaders_iff result complete header

/-- With complete evidence, membership is the union of the path-defined
member sets of all backedge occurrences at this header. -/
theorem mem_loop_iff {loops : List (HeaderLoop Label)}
    (result : loops? tree blocks = some loops) (complete : tree.Complete)
    {loop : HeaderLoop Label} (listed : loop ∈ loops) (b : BlockId Label) :
    b ∈ loop.members ↔
      ∃ edge, ActualBackedge cfg edge ∧ edge.header = loop.header ∧ Member cfg edge b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.mem_loop_iff result complete listed b

/-- The forest check admits the coalesced family exactly when its pairs
are disjoint or strictly nested. -/
theorem forest_eq_some_iff (loops : List (HeaderLoop Label)) :
    forest? tree blocks = some loops ↔ loops? tree blocks = some loops ∧ loops.Pairwise Compatible :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.forest_eq_some_iff loops

/-- Under complete evidence, the list whose length defines depth contains
exactly the distinct enclosing headers, whose member sets form a
strict inclusion chain. -/
theorem enclosing_spec {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops) (complete : tree.Complete)
    (b : BlockId Label) :
    let family := enclosing tree loops b
    (family.map HeaderLoop.header).Nodup ∧
      family.Pairwise (fun a b => StrictInside a b ∨ StrictInside b a) ∧
      ∀ header, header ∈ family.map HeaderLoop.header ↔
        ∃ edge, ActualBackedge cfg edge ∧ edge.header = header ∧ Member cfg edge b :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.enclosing_spec admitted complete b

/-- Successful placement is an enumerated, legal CFG cut. -/
theorem choosePlacement_sound {operands : List (Point Label)} {uses : List (Use Label)}
    {chosen : Point Label} (found : choosePlacement tree blocks operands uses = some chosen) :
    chosen ∈ candidateCuts cfg blocks ∧ Legal cfg operands uses chosen :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.choosePlacement_sound found

/-- The selected cut minimizes the derived depth among accepted cuts
and maximizes the supplied dominator address length at equal depth. -/
theorem choosePlacement_minimal {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops)
    {operands : List (Point Label)} {uses : List (Use Label)} {chosen other : Point Label}
    (found : choosePlacement tree blocks operands uses = some chosen)
    (candidate : other ∈ candidateCuts cfg blocks)
    (checked : checkPlacement tree operands uses other = true) :
    depth tree loops chosen.block ≤ depth tree loops other.block ∧
      (depth tree loops chosen.block = depth tree loops other.block →
        (tree.address other.block).length ≤ (tree.address chosen.block).length) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.choosePlacement_minimal admitted found candidate checked

/-- After forest admission, complete dominance and reachability evidence
makes failure equivalent to the absence of a represented legal cut. -/
theorem choosePlacement_complete {loops : List (HeaderLoop Label)}
    (admitted : forest? tree blocks = some loops)
    (complete : tree.Complete) (operands : List (Point Label)) (uses : List (Use Label)) :
    choosePlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopForest.choosePlacement_complete admitted complete operands uses

end Silmaril.SSA.SeaOfNodes.GCM.LoopForest
