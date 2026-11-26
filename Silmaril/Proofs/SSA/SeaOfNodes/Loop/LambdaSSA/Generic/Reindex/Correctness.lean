module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Defs
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex

open Silmaril.SSA
open SeaOfNodes
open Loop Loop.LambdaSSA.Generic
open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (Atom Primitive encodeTuple encodeTuple_injective inputEnv instruction
  instruction_deterministic terminatorRegion)
open RVSDG (Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

universe u v w x

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data} {σ : Type x}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out)

theorem header_incoming_roundtrip (incoming : HeaderIncoming g) :
    headerIncoming g (sourceArrival g incoming) = incoming := by
  rcases incoming with ⟨⟨site, successor⟩, target⟩
  cases site with
  | preheader => cases successor; rfl
  | header =>
    cases successor with
    | left jump => cases jump; rfl
    | right jump => cases jump; cases target

theorem slot_branch_eq (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2) :
    slotBranch g order slot = .br 0 (order slot).val.argument := by
  unfold slotBranch slotColumn
  generalize order slot = incoming
  rw [← header_incoming_roundtrip g incoming]
  cases sourceArrival g incoming <;> rfl

variable (m : Model.{u,v,w} Op)

theorem slot_transfer_iff (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2)
    (old : Env (Atom m)) (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) old (terminatorRegion (slotBranch g order slot))
        start label payload finish ↔
      label = 0 ∧ payload = PhiView.readArguments (slotColumn g order slot) old ∧ finish = start := by
  rw [slot_branch_eq]
  unfold slotColumn
  generalize order slot = incoming
  rw [← header_incoming_roundtrip g incoming]
  cases sourceArrival g incoming with
  | entry =>
    exact PhiView.latch_eq_transfer (instruction m) (phiView g) (edge g .entry)
      old start finish label payload
  | backedge =>
    exact PhiView.latch_eq_transfer (instruction m) (phiView g) (edge g .backedge)
      old start finish label payload

variable (input : Tuple (Val m.value) (dataPorts inputs))
variable (old next : Tuple (Val m.value) (dataPorts carried))

theorem header_backedge_iff (start finish : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m input) (encodeTuple m old))
        (header g) start 0 (encodeTuple m next) finish ↔
      g.step m input old = .inr next ∧ finish = start := by
  constructor
  · intro run
    have exactRun := run.deterministic (instruction_deterministic m) (header_eval g m input old start)
    cases step : g.step m input old with
    | inl result => simp [step, stepLabel] at exactRun
    | inr feedback =>
      have same : next = feedback := encodeTuple_injective m carried
        (by simpa only [step, stepPayload] using exactRun.2.1)
      exact ⟨congrArg Sum.inr same.symm, exactRun.2.2⟩
  · rintro ⟨step, same⟩
    subst finish
    simpa only [step, stepLabel, stepPayload] using header_eval g m input old start

end Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex
