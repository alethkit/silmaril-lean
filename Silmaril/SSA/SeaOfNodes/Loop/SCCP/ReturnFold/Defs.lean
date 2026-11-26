module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms
public import Silmaril.SSA.SeaOfNodes.GVN.Defs

/-! Materialize a proved constant at the return of an existing native loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold

open Diamond (Dataflow Model Signature Ty ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact)
open RVSDG (Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}

/-- One nullary producer appended to a typed table, with old wires embedded
into the extended scope and a wire for the new result. -/
structure Appended (Op : Signature.{u, v} Data) (args : List (Ty Data))
    (past sigs : List (List (Ty Data))) (out : ValueSort Data) where
  flow : Dataflow Op args past (sigs ++ [[.value out]])
  keep {t : Ty Data} : Origin args (extend past sigs) t → Origin args (extend past (sigs ++ [[.value out]])) t
  result : Origin args (extend past (sigs ++ [[.value out]])) (.value out)

def appendLiteral (literal : Op [] out) :
    {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs → Appended Op args past sigs out
  | _, _, .nil =>
    ⟨.cons literal .nil .nil, GVN.weaken [RVSDG.PortType.value out], GVN.newest .head⟩
  | _, _, .cons op wires rest =>
    let added := appendLiteral literal rest
    ⟨.cons op wires added.flow, added.keep, added.result⟩

/-- Append a literal in the native header and redirect just the return wire.
The earlier producer table, predicate, and feedback wires retain their scopes
and meanings under the embedding. -/
def withLiteral (g : Graph Op inputs carried entrySigs headerSigs out) (literal : Op [] out) :
    Graph Op inputs carried entrySigs (headerSigs ++ [[.value out]]) out :=
  let added := appendLiteral literal g.header
  { preheader := g.preheader
    header := added.flow
    phiInputs
      | .entry => g.phiInputs .entry
      | .backedge => (g.phiInputs .backedge).map (fun _ wire => added.keep wire)
    predicate := added.keep g.predicate
    result := added.result }

/-- The caller supplies literal opcodes from the same signature and proves
their interpretation in the model used for analysis. -/
structure Literals (m : Model.{u, v, w} Op) (out : ValueSort Data) where
  opcode : sortValue m.value out → Op [] out
  run_opcode (value : sortValue m.value out) : m.run (opcode value) .nil = value

inductive Refusal where
  | unseen
  | overdefined
  deriving DecidableEq, Repr

/-- Rewrite only an exact SCCP return fact. The two nonconstant cases
remain distinguishable at the interface. -/
def rewrite (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts carried)]
    (g : Graph Op inputs carried entrySigs headerSigs out) (input : Tuple (Fact m.value) (dataPorts inputs))
    (literals : Literals m out) : Except Refusal (Graph Op inputs carried entrySigs (headerSigs ++ [[.value out]]) out) :=
  match (SCCP.solve m g input).2.2 with
  | .constant value => .ok (withLiteral g (literals.opcode value))
  | .bottom => .error .unseen
  | .overdefined => .error .overdefined

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold
