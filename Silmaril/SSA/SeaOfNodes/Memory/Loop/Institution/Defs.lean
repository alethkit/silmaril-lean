module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

/-! Native equations of tail-tested memory loops over typed entry ports. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution

open CategoryTheory Silmaril.Logic.Institution
open Memory.Diamond.Institution (Signature Model mapBody)

variable {P Q : Signature} {args target : List ValueSort}
variable {past : List (List ValueSort)} {version : Nat}

/-- Typed entry renaming retains the admitted load and store occurrences. -/
theorem accesses_mapBody (rename : Memory.Diamond.Institution.PortMap args target)
    (body : Body args past version) :
    accesses (mapBody rename body) = accesses body := by
  induction body <;> simp only [mapBody, accesses, *]

/-- Rename both the ordered body and the invariant stop-word port. -/
def mapGraph (h : P ⟶ Q) (graph : Graph P.args) : Graph Q.args where
  body := mapBody (Signature.Hom.port h) graph.body
  effects := (accesses_mapBody _ _).trans graph.effects
  stop := Signature.Hom.port h graph.stop

structure Equation (P : Signature) where
  lhs : Graph P.args
  rhs : Graph P.args

def Equation.map (h : P ⟶ Q) (e : Equation P) : Equation Q :=
  ⟨mapGraph h e.lhs, mapGraph h e.rhs⟩

/-- Compare partial word/heap observations at each initial heap. The model
supplies the ordered input tuple and initialized cell count. -/
def Equation.Holds (e : Equation P) (model : Model P) : Prop :=
  ∀ initial, e.lhs.denote model.input initial = e.rhs.denote model.input initial

/-- A room over the same typed entry valuations as the memory diamond. -/
def room (P : Signature) : Room.{0, 0, 0} where
  Sen := Equation P
  Mod := Cat.of (Discrete (Model P))
  Sat model e := e.Holds model.as

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution
