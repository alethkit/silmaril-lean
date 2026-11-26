module

public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Defs
public import Mathlib.Logic.Equiv.Defs

/-! # Positional views of the actual incoming loop occurrences -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic

open Diamond (ValueSort dataPorts)
open Diamond.LambdaSSA (Primitive portCode)
open Silmaril.Isotope.LambdaSSA (Terminator)

universe u v

variable {Data : Type u} {Op : Diamond.Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Diamond.Ty Data))} {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out)

/-- A successor occurrence of the emitted terminators whose target is the header. -/
abbrev HeaderIncoming := PhiView.Incoming (terminators g) 0

def headerIncoming (arrival : Incoming) : HeaderIncoming g := ⟨edge g arrival, by cases arrival <;> rfl⟩

def sourceArrival (incoming : HeaderIncoming g) : Incoming :=
  match incoming.val.source with
  | .preheader => .entry
  | .header => .backedge

/-- An order enumerates the header's occurrences. Each position selects
one complete argument column in that occurrence's scope. -/
def slotColumn (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2) :
    PhiView.Arguments ((sourceTyping g).scope (order slot).val) ((dataPorts carried).map portCode) :=
  fun i => (phiView g).table 0 i (order slot)

def slotBranch (order : Fin 2 ≃ HeaderIncoming g) (slot : Fin 2) : Terminator (Primitive Op) :=
  .br 0 (PhiView.packTerm (slotColumn g order slot))

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic
