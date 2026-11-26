module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.HeaderUse.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic
open Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass
open Activation (Inputs View)
open Deletion (DeletedLoop)
open Diamond (Dataflow Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {flow : Dataflow Op args past sigs} {out : ValueSort Data}

private theorem producer_mem (candidate : Producer flow out) :
    (⟨out, candidate⟩ : Σ sort, Producer flow sort) ∈ producers flow := by
  induction candidate with
  | here => exact List.mem_cons_self
  | later ref ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨_, ref⟩, ih, rfl⟩)

variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {n : Nat} {sorts : Fin n → ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {g : Cyclic.Graph Op inputs sorts} {p : Partition n}
variable {result : DeletedLoop Op inputs carried entrySigs out}

theorem firstDeletion_none (loop : Loop.Graph Op inputs carried entrySigs headerSigs out) :
    firstDeletion? loop = none ↔
      ∀ {sort} (candidate : Producer loop.header sort), Deletion.delete? loop candidate = none := by
  unfold firstDeletion?
  rw [List.findSome?_eq_none_iff]
  exact ⟨fun exhausted sort candidate => exhausted ⟨sort, candidate⟩ (producer_mem candidate),
    fun exhausted ⟨_, candidate⟩ _ => exhausted candidate⟩

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

private inductive Accepted (view : View g loop) (p : Partition n)
    (result : DeletedLoop Op inputs carried entrySigs out) : Prop where
  | direct {sort : ValueSort Data} (candidate : Producer loop.header sort)
      (deleted : Deletion.delete? loop candidate = some result)
  | afterRedirect (edit : Redirect loop sorts)
      (edited : Loop.Graph Op inputs carried entrySigs headerSigs out)
      (redirected : HeaderUse.redirect? view p edit.consumer edit.use edit.original
        edit.representative edit.wire = some edited)
      {sort : ValueSort Data} (candidate : Producer edited.header sort)
      (deleted : Deletion.delete? edited candidate = some result)

theorem step_none (view : View g loop) :
    step? view = none ↔
      ∀ proposal ∈ proposals view, tryProposal? view (FixedPoint.normalize g) proposal = none :=
  List.findSome?_eq_none_iff

theorem step_witness (view : View g loop) (found : step? view = some result) :
    ∃ proposal ∈ proposals view, tryProposal? view (FixedPoint.normalize g) proposal = some result :=
  List.exists_of_findSome?_eq_some found

private theorem accepted (view : View g loop) (found : step? view = some result) :
    Accepted view (FixedPoint.normalize g) result := by
  obtain ⟨proposal, _, success⟩ := step_witness view found
  cases proposal with
  | delete candidate => exact .direct candidate success
  | redirect edit =>
    unfold tryProposal? at success
    cases redirected : HeaderUse.redirect? view (FixedPoint.normalize g) edit.consumer edit.use
        edit.original edit.representative edit.wire with
    | none => simp [redirected] at success
    | some edited =>
      simp only [redirected, Option.bind_some, firstDeletion?] at success
      obtain ⟨⟨_, candidate⟩, _, deleted⟩ := List.exists_of_findSome?_eq_some success
      exact .afterRedirect edit edited redirected candidate deleted

theorem step_count (view : View g loop) (found : step? view = some result) :
    result.headerSigs.length + 1 = headerSigs.length := by
  cases accepted view found with
  | direct _ deleted => exact Deletion.delete_count deleted
  | afterRedirect _ _ _ _ deleted => exact Deletion.delete_count deleted

variable (m : Model.{u,v,w} Op) (input : Inputs m inputs)

theorem step_initial (view : View g loop) (found : step? view = some result) :
    result.graph.initial m input = loop.initial m input := by
  cases accepted view found with
  | direct _ deleted => exact Deletion.delete_initial deleted m input
  | afterRedirect edit _ redirected _ deleted =>
    exact (Deletion.delete_initial deleted m input).trans
      (HeaderUse.redirect_initial view edit.consumer edit.use edit.original edit.representative
        edit.wire redirected m input)

theorem step_activation (view : View g loop) (found : step? view = some result)
    (old : Inputs m carried) (invariant : view.LatchesAgree (FixedPoint.normalize g) m old old) :
    result.graph.step m input old = loop.step m input old := by
  cases accepted view found with
  | direct _ deleted => exact Deletion.delete_step deleted m input old
  | afterRedirect edit _ redirected _ deleted =>
    exact (Deletion.delete_step deleted m input old).trans
      (HeaderUse.redirect_step view edit.consumer edit.use edit.original edit.representative
        edit.wire redirected m input old invariant).2.1

theorem step_eval (view : View g loop) (found : step? view = some result) (budget : Nat) :
    result.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  cases accepted view found with
  | direct _ deleted => exact Deletion.delete_evalBackedges deleted m input budget
  | afterRedirect edit _ redirected _ deleted =>
    exact (Deletion.delete_evalBackedges deleted m input budget).trans
      (HeaderUse.redirect_evalBackedges view edit.consumer edit.use edit.original edit.representative
        edit.wire redirected m input budget)

theorem step_returns (view : View g loop) (found : step? view = some result) (value : sortValue m.value out) :
    result.graph.Returns m input value ↔ loop.Returns m input value := by
  cases accepted view found with
  | direct _ deleted => exact Deletion.delete_returns deleted m input value
  | afterRedirect edit _ redirected _ deleted =>
    exact (Deletion.delete_returns deleted m input value).trans
      (HeaderUse.redirect_returns view edit.consumer edit.use edit.original edit.representative
        edit.wire redirected m input value)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass
