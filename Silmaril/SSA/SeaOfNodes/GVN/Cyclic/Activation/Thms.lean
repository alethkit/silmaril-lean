module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.Correctness
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation

open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {p : Partition n} {m : Model.{u,v,w} Op}

variable (view : View g loop)
variable {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}

/-- The actual entry column establishes class agreement of the first latches. -/
theorem View.initial_agrees (stable : Stable g p) (fixed : InputsAgree m input₁ input₂) :
    view.LatchesAgree p m (loop.initial m input₁) (loop.initial m input₂) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.initial_agree view stable fixed

/-- With related arguments and latches, class members read the same typed
value from the actual header evaluation. -/
theorem View.header_agrees (stable : Stable g p) (fixed : InputsAgree m input₁ input₂)
    (latches : view.LatchesAgree p m old₁ old₂) :
    view.ClassesAgree p m input₁ old₁ input₂ old₂ :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.classes_agree view stable fixed latches

/-- Equal typed operand keys give equal reads in related completed headers. -/
theorem View.read_agrees (fixed : InputsAgree m input₁ input₂)
    (classes : view.ClassesAgree p m input₁ old₁ input₂ old₂)
    (a b : Source inputs sorts t) (same : a.address.relabel p = b.address.relabel p) :
    headerRead loop m input₁ old₁ (sourceWire view.site a) =
      headerRead loop m input₂ old₂ (sourceWire view.site b) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.read_source_agrees view fixed classes a b same

/-- Related activations read equal guards. A taken backedge preserves latch
agreement, and an exit returns equal observed values. -/
theorem View.step_agrees (stable : Stable g p) (fixed : InputsAgree m input₁ input₂)
    (latches : view.LatchesAgree p m old₁ old₂) :
    headerRead loop m input₁ old₁ loop.predicate = headerRead loop m input₂ old₂ loop.predicate ∧
      view.OutcomesAgree p m (loop.step m input₁ old₁) (loop.step m input₂ old₂) :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.step_agrees view stable fixed latches

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

/-- The executable return-wire substitution preserves the ordinary evaluator
for every backedge budget and every typed input. -/
theorem View.redirect_evalBackedges (p : Partition n) (replacement : Source inputs sorts out)
    (m : Model.{u,v,w} Op) (input : Inputs m inputs) (budget : Nat) :
    (view.redirectResult p replacement).evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Activation.redirect_eval view p replacement m input budget

/-- The rewritten and original loops have the same finite returns. -/
theorem View.redirect_returns (p : Partition n) (replacement : Source inputs sorts out)
    (m : Model.{u,v,w} Op) (input : Inputs m inputs) (value : sortValue m.value out) :
    (view.redirectResult p replacement).Returns m input value ↔ loop.Returns m input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges, view.redirect_evalBackedges]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation
