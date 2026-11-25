module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.SingleTheta.Thms
import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Thms
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Environments

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs

open Continuation.Partial
open Continuation.Descent (Pending)
open Isomorphism.Invocation (loopVertex)
open Isomorphism.Proofs (LocalsRelated read_same)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {ids : GlobalRel}
variable {primitives : Primitives m σ} {mapping : Renaming}
variable {args entry carried returned outs : Ports (Ty V S)} {extra : Nat}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {left : NestedTheta.Term (Instruction Op) args [] sigsL outs}
variable {right : NestedTheta.Term (Instruction Op) args [] sigsR outs}
variable {inputL inputR : Tuple m.Val args} {store : σ}
variable {locL locR : Location} {stopL stopR : Block m σ outs}

theorem block_observations
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    locR = locL.rename mapping ∧ SitesRelated m ids stopL.site stopR.site ∧ stopL.store = stopR.store := by
  induction stopped with
  | acyclic _ sites _ _ => exact ⟨rfl, sites, rfl⟩
  | theta _ _ _ _ _ _ _ sites _ _ => exact ⟨rfl, sites, rfl⟩
  | gamma _ _ _ _ _ ih => exact ⟨congrArg (Location.gamma _) ih.1, ih.2⟩

theorem block_evals
    (stopped : BlockPair primitives ids mapping left right inputL inputR store locL locR stopL stopR) :
    Eval primitives (.region left inputL PUnit.unit) store stopL.outcome ∧
    Eval primitives (.region right inputR PUnit.unit) store stopR.outcome := by
  induction stopped with
  | acyclic _ _ ranL ranR => exact ⟨ranL.eval, ranR.eval⟩
  | @theta _ _ _ sigsL sigsR map left right _ _ _ _ first current _ _ _ _
      initial outputs startsL startsR startsStore completed location sites firstL firstR =>
    have done : SingleTheta.Finishes primitives (map.child 0 0) left right first _ _ :=
      ⟨current, completed, .blocked location sites firstL firstR⟩
    obtain ⟨ranL, ranR⟩ := done.eval
    rw [startsL, startsStore] at ranL
    rw [startsR, startsStore] at ranR
    exact ⟨.bindBlocked (node := loopVertex initial sigsL) (.theta ranL),
      .bindBlocked (node := loopVertex initial sigsR) (.theta ranR)⟩
  | @gamma _ _ _ _ extra _ sigsL sigsR armsL armsR entryL entryR _ _ store tag _ _ stopL stopR
      inputs outputs selectedL selectedR _ ih =>
    obtain ⟨childL, childR⟩ := ih
    cases stopL
    cases stopR
    refine ⟨.bindBlocked (node := vertex inputs sigsL) ?_, .bindBlocked (node := vertex inputs sigsR) ?_⟩
    · exact selectedL.symm ▸ Eval.gamma (cs := sigsL) (children := armsL) childL
    · exact selectedR.symm ▸ Eval.gamma (cs := sigsR) (children := armsR) childR

private theorem selected_tuple {valuesL valuesR : Tuple m.Val (.control (extra + 2) :: entry)}
    (related : TupleRelated m ids valuesL valuesR) :
    ∃ tag nextL nextR, valuesL = .cons (.control tag) nextL ∧ valuesR = .cons (.control tag) nextR ∧
      TupleRelated m ids nextL nextR := by
  cases related with
  | cons head tail =>
    cases head with
    | control tag => exact ⟨tag, _, _, rfl, rfl, tail⟩

/-- γ congruence uses the related selector to choose a single pair of arms.
All three outcomes keep the enclosing frame or resume its wiring suffix. -/
theorem gamma
    {childSigsL childSigsR : Fin (extra + 2) → List (Ports (Ty V S))}
    {armsL : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsL i) returned}
    {armsR : (i : Fin (extra + 2)) → NestedTheta.Term (Instruction Op) entry [] (childSigsR i) returned}
    (inputs : Wires args [] (.control (extra + 2) :: entry)) (outputs : Wires args [returned] outs)
    (arms : ∀ tag {nextL nextR : Tuple m.Val entry}, TupleRelated m ids nextL nextR →
      RegionPair primitives ids (mapping.child 0 tag.val) (armsL tag) (armsR tag) nextL nextR store)
    (related : TupleRelated m ids inputL inputR) :
    RegionPair primitives ids mapping (code inputs armsL outputs) (code inputs armsR outputs) inputL inputR store := by
  obtain ⟨tag, nextL, nextR, selectL, selectR, values⟩ :=
    selected_tuple (read_same related LocalsRelated.empty inputs)
  cases arms tag values with
  | @returned _ _ finalStore paired ranL ranR =>
    have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl paired
    refine .returned (finalStore := finalStore) (read_same related locals outputs)
      (.bind (node := vertex inputs childSigsL) ?_ (.ret outputs _ _ _))
      (.bind (node := vertex inputs childSigsR) ?_ (.ret outputs _ _ _))
    · exact selectL.symm ▸ Eval.gamma (cs := childSigsL) (children := armsL) ranL
    · exact selectR.symm ▸ Eval.gamma (cs := childSigsR) (children := armsR) ranR
  | blocked stopped => exact .blocked (.gamma inputs outputs selectL selectR stopped)
  | productive run =>
    cases run with
    | @reached _ _ _ _ _ _ pendingL pendingR paired ranL ranR =>
      refine .productive (.reached
        (pendingL := .bind (past := []) (.ret outputs) inputL PUnit.unit pendingL)
        (pendingR := .bind (past := []) (.ret outputs) inputR PUnit.unit pendingR)
        paired (.inside (node := vertex inputs childSigsL) ?_) (.inside (node := vertex inputs childSigsR) ?_))
      · exact selectL.symm ▸ Feedback.Reaches.gamma (cs := childSigsL) (children := armsL) ranL
      · exact selectR.symm ▸ Feedback.Reaches.gamma (cs := childSigsR) (children := armsR) ranR

private theorem enter_theta {body : SingleTheta.Body Op carried sigsL}
    (initial : Wires args [] carried) (outputs : Wires args [carried] outs) (input : Tuple m.Val args) (store : σ) :
    Feedback.Reaches primitives (.region (SingleTheta.code initial body outputs) input PUnit.unit) store
      ⟨carried, sigsL, embed body.toTerm, (initial.read input PUnit.unit, store)⟩
      (.bind (past := []) (.ret outputs) input PUnit.unit .empty) :=
  .inside (node := loopVertex initial sigsL)
    (.theta (.restart (input := (initial.read input PUnit.unit, store))
      (current := (initial.read input PUnit.unit, store)) .refl))

private theorem theta {bodyL : SingleTheta.Body Op carried sigsL} {bodyR : SingleTheta.Body Op carried sigsR}
    (initial : Wires args [] carried) (outputs : Wires args [carried] outs)
    (admitted : OrderedGraph (mapping.child 0 0) bodyL bodyR)
    (respects : ActionsRespect primitives ids) (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping (SingleTheta.code initial bodyL outputs)
      (SingleTheta.code initial bodyR outputs) inputL inputR store := by
  let first : SingleTheta.Carries m ids σ carried :=
    ⟨initial.read inputL PUnit.unit, initial.read inputR PUnit.unit,
      read_same inputs LocalsRelated.empty initial, store⟩
  rcases SingleTheta.loop_observations admitted respects first with ⟨_, _, finished⟩ | productive
  · have ran := finished.eval
    obtain ⟨current, completed, terminal⟩ := finished
    cases terminal with
    | @exited _ _ _ finalStore _ values _ _ =>
      have locals := LocalsRelated.empty.snoc (fun _ _ same => same) rfl values
      exact .returned (finalStore := finalStore) (read_same inputs locals outputs)
        (.bind (node := loopVertex initial sigsL) (.theta ran.1) (.ret outputs _ _ _))
        (.bind (node := loopVertex initial sigsR) (.theta ran.2) (.ret outputs _ _ _))
    | blocked location sites firstL firstR =>
      exact .blocked (.theta initial outputs rfl rfl rfl completed location sites firstL firstR)
  · exact .productive (.reached productive
      (enter_theta initial outputs inputL store) (enter_theta initial outputs inputR store))

theorem regions (admitted : CodePair Op mapping left right) (respects : ActionsRespect primitives ids)
    (inputs : TupleRelated m ids inputL inputR) (store : σ) :
    RegionPair primitives ids mapping left right inputL inputR store := by
  induction admitted generalizing store with
  | acyclic admitted =>
    obtain ⟨_, _, paired⟩ := Local.graph_evaluate admitted respects inputs store
    cases paired with
    | returned values ranL ranR => exact .returned values ranL ranR
    | blocked location sites ranL ranR => exact .blocked (.acyclic location sites ranL ranR)
  | theta initial outputs _ admitted => exact theta initial outputs admitted respects inputs store
  | gamma wiring outputs _ _ children =>
    exact gamma wiring outputs (by
      intro tag _ _ paired
      exact children tag paired store) inputs

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.Local.Gamma.Proofs
