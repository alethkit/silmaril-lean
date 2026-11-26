module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Native equations for initialized-cell memory diamonds. Signature maps
rename typed entry ports. The Boolean guard and heap operations are intrinsic. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG (Origin Port Tuple)

abbrev PortMap (args target : List ValueSort) :=
  ∀ {sort}, Port args sort → Port target sort

/-- The ordered scalar boundary of a memory diamond. -/
structure Signature where
  args : List ValueSort

structure Signature.Hom (P Q : Signature) where
  port : PortMap P.args Q.args

instance : Category Signature where
  Hom := Signature.Hom
  id _ := ⟨fun p => p⟩
  comp h k := ⟨fun p => k.port (h.port p)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable {P Q : Signature}
variable {args target : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}

/-- Extend the map under the word exported by the selected arm. -/
def liftPortMap (rename : PortMap args target) : PortMap (.word :: args) (.word :: target)
  | _, .head => .head
  | _, .tail p => .tail (rename p)

def mapOrigin (rename : PortMap args target) {sort : ValueSort} :
    Origin args past sort → Origin target past sort
  | .arg p => .arg (rename p)
  | .output node p => .output node p

/-- Rename entry uses while preserving all local producers and memory edges. -/
def mapBody (rename : PortMap args target) :
    {past : List (List ValueSort)} → {version : Nat} →
    Body args past version → Body target past version
  | _, _, .ret mem value => .ret mem (mapOrigin rename value)
  | _, _, .load mem address rest => .load mem (mapOrigin rename address) (mapBody rename rest)
  | _, _, .store mem address value rest =>
    .store mem (mapOrigin rename address) (mapOrigin rename value) (mapBody rename rest)

/-- Translate both arms and the suffix while retaining the exact Region order. -/
def mapGraph (h : P ⟶ Q) (graph : Graph P.args) : Graph Q.args where
  merge := graph.merge
  arm edge := mapBody (Signature.Hom.port h) (graph.arm edge)
  suffix := mapBody (liftPortMap (Signature.Hom.port h)) graph.suffix

/-- Form the source input tuple by looking up the target port for every source port. -/
def pullInput : {args : List ValueSort} → PortMap args target →
    Tuple (Val cells) target → Tuple (Val cells) args
  | [], _, _ => .nil
  | _ :: _, rename, input =>
    .cons (input.get (rename .head)) (pullInput (fun p => rename (.tail p)) input)

/-- A heap size and an interpretation of all typed entry ports. The guard
and initial heap can vary at each call. -/
structure Model (P : Signature) where
  cells : Nat
  input : Tuple (Val cells) P.args

def reduct (h : P ⟶ Q) (model : Model Q) : Model P :=
  ⟨model.cells, pullInput (Signature.Hom.port h) model.input⟩

/-- The observation shared with the occurrence-indexed source rules. -/
def Model.observe (model : Model P) (graph : Graph P.args) (guard : Bool)
    (initial : Heap model.cells) : Word × Heap model.cells :=
  graph.denote guard model.input initial

structure Equation (P : Signature) where
  lhs : Graph P.args
  rhs : Graph P.args

def Equation.map (h : P ⟶ Q) (e : Equation P) : Equation Q :=
  ⟨mapGraph h e.lhs, mapGraph h e.rhs⟩

/-- Agreement of the returned word and the entire final heap at every guard
and initialized heap, with the scalar entry valuation supplied by the model. -/
def Equation.Holds (e : Equation P) (model : Model P) : Prop :=
  ∀ guard initial, model.observe e.lhs guard initial = model.observe e.rhs guard initial

def room (P : Signature) : Room.{0, 0, 0} where
  Sen := Equation P
  Mod := Cat.of (Discrete (Model P))
  Sat model e := e.Holds model.as

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution
