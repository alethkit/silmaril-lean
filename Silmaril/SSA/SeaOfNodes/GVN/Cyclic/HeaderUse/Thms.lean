module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Correctness
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse

open Diamond (Model Signature Ty ValueSort dataPorts sortValue)
open RVSDG (Origin Port)
open Elimination (inFinal operandScope)
open Activation (View Inputs sourceWire headerRead)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out sort consumerOut : ValueSort Data} {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop rewritten : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {p : Partition n}
variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

variable (view : View g loop) (consumer : Producer loop.header consumerOut)
variable (use : Port (dataPorts consumer.key.ins) (.value sort))
variable (original representative : Source inputs sorts sort)
variable (prefixWire : Origin (Loop.headerPorts inputs carried) (operandScope consumer) (.value sort))

/-- Acceptance identifies the original use and verifies that the proposed
representative is the supplied typed wire in the consumer's actual prefix. -/
theorem check_eq_true_iff :
    check view p consumer use original representative prefixWire = true ↔
      Stable g p ∧ original.address.relabel p = representative.address.relabel p ∧
        inFinal consumer (operandAt consumer use) = sourceWire view.site original ∧
        inFinal consumer prefixWire = sourceWire view.site representative :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.check_correct
    view consumer use original representative prefixWire

variable (accepted : redirect? view p consumer use original representative prefixWire = some rewritten)
include accepted
variable (m : Model.{u,v,w} Op) (input : Inputs m inputs)

/-- The initial latch tuple is exactly the same. -/
theorem redirect_initial :
    rewritten.initial m input = loop.initial m input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.redirect_initial
    view consumer use original representative prefixWire accepted m input

/-- At a class-consistent original state the guard and the full step agree.
A taken backedge reestablishes the original class invariant for the common
next state, relating the two executions for the next activation. -/
theorem redirect_step (old : Inputs m carried) (invariant : view.LatchesAgree p m old old) :
    headerRead rewritten m input old rewritten.predicate = headerRead loop m input old loop.predicate ∧
      rewritten.step m input old = loop.step m input old ∧
      ∀ next, rewritten.step m input old = .inr next → view.LatchesAgree p m next next :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.redirect_step
    view consumer use original representative prefixWire accepted m input old invariant

/-- Every bounded evaluation from the actual entry agrees. -/
theorem redirect_evalBackedges (budget : Nat) :
    rewritten.evalBackedges m budget input = loop.evalBackedges m budget input :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.redirect_eval
    view consumer use original representative prefixWire accepted m input budget

/-- The original and rewritten loops have exactly the same finite returns. -/
theorem redirect_returns (value : sortValue m.value out) :
    rewritten.Returns m input value ↔ loop.Returns m input value := by
  simp only [Loop.Graph.returns_iff_evalBackedges,
    redirect_evalBackedges view consumer use original representative prefixWire accepted m input]

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse
