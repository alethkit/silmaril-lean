module

public import Silmaril.SSA.SeaOfNodes.GCM.Discovery.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Correctness

/-! # Certification of finite placement discovery -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result}
variable {operands : List (Point Label)} {uses : List (Use Label)} {candidate : Point Label}

/-- The enumeration includes all and only in-bounds cuts of represented blocks. -/
theorem mem_candidateCuts (blocks : List (Target Label)) (point : Point Label) :
    point ∈ candidateCuts cfg blocks ↔
      point.block ∈ (none :: blocks.map some) ∧ point.cut ≤ (shape cfg point.block).bindings :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.mem_candidateCuts blocks point

/-- A result names an enumerated cut and passes the existing legality checker. -/
theorem discoverPlacement_sound (tree : DominatorTree cfg) (blocks : List (Target Label))
    (found : discoverPlacement tree blocks operands uses = some candidate) :
    candidate ∈ candidateCuts cfg blocks ∧ checkPlacement tree operands uses candidate = true :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.discoverPlacement_sound tree blocks found

/-- Failure means that the checker rejects every enumerated cut. -/
theorem discoverPlacement_eq_none_iff (tree : DominatorTree cfg) (blocks : List (Target Label))
    (operands : List (Point Label)) (uses : List (Use Label)) :
    discoverPlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, checkPlacement tree operands uses point = false :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.discoverPlacement_eq_none_iff tree blocks operands uses

/-- With complete tree evidence, failure excludes semantic legality at every
enumerated cut. Sound-only certificates can omit legal cuts from acceptance. -/
theorem discoverPlacement_eq_none_iff_no_legal (tree : DominatorTree cfg) (complete : tree.Complete)
    (blocks : List (Target Label)) (operands : List (Point Label)) (uses : List (Use Label)) :
    discoverPlacement tree blocks operands uses = none ↔
      ∀ point ∈ candidateCuts cfg blocks, ¬ Legal cfg operands uses point :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.discoverPlacement_eq_none_iff_no_legal
    tree complete blocks operands uses

end Silmaril.SSA.SeaOfNodes.GCM
