module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass

open Activation (Inputs View)
open Deletion (DeletedLoop)
open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts}
variable {result : DeletedLoop Op inputs carried entrySigs out}

/-- The deletion scan covers every typed producer in the given header. -/
theorem firstDeletion?_eq_none_iff (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    firstDeletion? loop = none ↔
      ∀ {sort} (candidate : Producer loop.header sort), Deletion.delete? loop candidate = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.firstDeletion_none loop

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]
variable (view : View g loop)

/-- Failure excludes every accepted shrinking proposal in this view's enumeration. -/
theorem step?_eq_none_iff :
    step? view = none ↔
      ∀ proposal ∈ proposals view, tryProposal? view (FixedPoint.normalize g) proposal = none :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_none view

/-- The returned loop comes from an enumerated proposal accepted by the checks. -/
theorem step?_accepted (found : step? view = some result) :
    ∃ proposal ∈ proposals view, tryProposal? view (FixedPoint.normalize g) proposal = some result :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_witness view found

variable (found : step? view = some result)
include found

/-- Every success removes exactly one header producer. -/
theorem step_count :
    result.headerSigs.length + 1 = headerSigs.length :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_count view found

variable (m : Model.{u,v,w} Op) (input : Inputs m inputs)

/-- The original and resulting loops have the same initial latch tuple. -/
theorem step_initial :
    result.graph.initial m input = loop.initial m input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_initial m input view found

/-- A step from a class-consistent original state preserves the full
activation transition, including the next backedge latch tuple. -/
theorem step_activation (old : Inputs m carried)
    (invariant : view.LatchesAgree (FixedPoint.normalize g) m old old) :
    result.graph.step m input old = loop.step m input old :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_activation m input view found old invariant

/-- Success preserves every bounded evaluation from entry. -/
theorem step_evalBackedges (budget : Nat) :
    result.graph.evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_eval m input view found budget

/-- Success preserves and reflects every finite return. -/
theorem step_returns (value : sortValue m.value out) :
    result.graph.Returns m input value ↔ loop.Returns m input value :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.step_returns m input view found value

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass
