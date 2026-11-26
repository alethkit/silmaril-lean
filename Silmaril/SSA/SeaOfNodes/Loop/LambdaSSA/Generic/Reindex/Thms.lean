module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Correctness

/-! # Exact edge readback for either predecessor order -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (Model Val ValueSort dataPorts)
open Diamond.LambdaSSA (Atom encodeTuple inputEnv instruction terminatorRegion)
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
    headerIncoming g (sourceArrival g incoming) = incoming :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.header_incoming_roundtrip g incoming

/-- Every actual incoming header occurrence is either the preheader jump
or the feedback successor, and their identities round-trip. -/
def headerIncomingEquiv : Incoming ≃ HeaderIncoming g where
  toFun := headerIncoming g
  invFun := sourceArrival g
  left_inv := fun arrival => by cases arrival <;> rfl
  right_inv := header_incoming_roundtrip g

theorem slot_branch_eq (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2) :
    slotBranch g order slot = .br 0 (order slot).val.argument :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.slot_branch_eq g order slot

/-- Read back an emitted branch through the position it occupies in any
ordered presentation of the header. This restores its exact packed term. -/
theorem slot_branch_roundtrip (order : Fin 2 ≃ HeaderIncoming g) (incoming : HeaderIncoming g) :
    slotBranch g order (order.symm incoming) = .br 0 incoming.val.argument := by
  rw [slot_branch_eq, Equiv.apply_symm_apply]

variable (m : Model.{u,v,w} Op)

/-- The branch from a positional view reads the entire selected column in
one old environment and changes neither its target nor ambient state. -/
theorem slot_transfer_iff (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2)
    (old : Env (Atom m)) (start finish : σ) (label : Nat) (payload : Value (Atom m)) :
    Semantics.Region.Eval (instruction m) old (terminatorRegion (slotBranch g order slot))
        start label payload finish ↔
      label = 0 ∧ payload = PhiView.readArguments (slotColumn g order slot) old ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.slot_transfer_iff
    g m order slot old start finish label payload

/-- A finite evaluation of the actual emitted header takes the backedge
with a typed tuple exactly when the native step selects that whole tuple. -/
theorem header_backedge_iff (input : Tuple (Val m.value) (dataPorts inputs))
    (old next : Tuple (Val m.value) (dataPorts carried)) (start finish : σ) :
    Semantics.Region.Eval (instruction m) (extend (inputEnv m input) (encodeTuple m old))
        (header g) start 0 (encodeTuple m next) finish ↔
      g.step m input old = .inr next ∧ finish = start :=
  Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.header_backedge_iff g m input old next start finish

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
