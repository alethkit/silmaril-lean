module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Thms

/-! Check and specialize the dispatcher of the fixed pure quad loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch

open Diamond (Model Signature ValueSort dataPorts)
open Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Replace only block 2's branch. The dispatcher still costs one native
block visit, and the selected block keeps its original index and body. -/
def specialize (p : Program Op regs out) (side : Bool) : Tail.Source Op regs out 5 :=
  fun index =>
    let block := p.source index
    if index = 2 then { block with terminator := .transfer (.jump (feedbackBlock side)) } else block

variable (m : Model.{u, v, w} Op) (p : Program Op regs out) [BankDecidableEq m.value (dataPorts regs)]
variable (input : Tuple (Fact m.value) (dataPorts regs))

/-- A specialization is tied to the abstract entry facts used to solve SCCP. -/
structure Checked where
  side : Bool
  marked : incomingIndex (.feedback side) ∈ (solve m p input).1
  excluded : incomingIndex (.feedback !side) ∉ (solve m p input).1

/-- Admit exactly one marked feedback route. Two marked routes or zero
marked routes leave the dispatcher unspecialized. -/
def check : Option (Checked m p input) :=
  let marks := (solve m p input).1
  if h : incomingIndex (.feedback true) ∈ marks ∧ incomingIndex (.feedback false) ∉ marks then
    some ⟨true, h.1, h.2⟩
  else if h : incomingIndex (.feedback false) ∈ marks ∧ incomingIndex (.feedback true) ∉ marks then
    some ⟨false, h.1, h.2⟩
  else none

variable {m p input}

/-- Emit the actual typed quad source for a successful check. -/
def Checked.source (checked : Checked m p input) : Tail.Source Op regs out 5 :=
  specialize p checked.side

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch
