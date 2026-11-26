module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Proofs

open Silmaril.Machine.RTL.SSA (Prog)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow)
open Silmaril.SSA.RVSDG (Origin Wires)
open Silmaril.SSA.RVSDG.NestedTheta.Equality (addresses_injective)

private theorem origin_eq {args : List PortTy} {past : List (List PortTy)} {t : PortTy}
    {left right : Origin args past t} (h : left.address = right.address) : left = right := by
  let lhs : Wires args past [t] := .cons left .nil
  let rhs : Wires args past [t] := .cons right .nil
  have same : lhs.addresses = rhs.addresses := congrArg List.singleton h
  exact congrArg (fun w : Wires args past [t] => w.get .head) (addresses_injective lhs rhs same)

private theorem table_eq {args : List PortTy} {past sigs : List (List PortTy)}
    (left : Dataflow SwapOp args past sigs) :
    ∀ right : Dataflow SwapOp args past sigs, tableCode left = tableCode right → left = right := by
  induction left with
  | nil =>
    intro right _
    cases right
    rfl
  | cons op operands rest ih =>
    intro right same
    cases right with
    | cons other otherOperands tail =>
      obtain ⟨headEq, tailEq⟩ := List.cons.inj same
      obtain ⟨opEq, operandsEq⟩ := Prod.mk.inj headEq
      cases op <;> cases other <;> cases opEq
      all_goals
        obtain rfl := addresses_injective _ _ operandsEq
        obtain rfl := ih _ tailEq
        rfl

private theorem graph_eq {left right : NativeGraph}
    (preheader : left.preheader = right.preheader) (header : left.header = right.header)
    (phi : left.phiInputs = right.phiInputs) (predicate : left.predicate = right.predicate)
    (result : left.result = right.result) : left = right := by
  cases left
  cases right
  cases preheader
  cases header
  cases phi
  cases predicate
  cases result
  rfl

private theorem graphCode_injective {left right : NativeGraph} (h : graphCode left = graphCode right) :
    left = right := by
  refine graph_eq (table_eq _ _ (congrArg GraphCode.preheader h))
    (table_eq _ _ (congrArg GraphCode.header h)) ?_
    (origin_eq (congrArg GraphCode.predicate h)) (origin_eq (congrArg GraphCode.result h))
  funext edge
  cases edge with
  | entry => exact addresses_injective _ _ (congrArg GraphCode.entry h)
  | backedge => exact addresses_injective _ _ (congrArg GraphCode.feedback h)

theorem lowerChecked_eq_some_iff (g : NativeGraph) (target : Prog Reg) :
    lowerChecked g = some target ↔ g = graph ∧ target = lower := by
  constructor
  · intro accepted
    unfold lowerChecked at accepted
    split at accepted
    · rename_i agrees
      exact ⟨graphCode_injective agrees, (Option.some.inj accepted).symm⟩
    · cases accepted
  · rintro ⟨rfl, rfl⟩
    simp [lowerChecked]

end Silmaril.Machine.SeaOfNodes.Loop.RTL.CarriedBank.Proofs
