module

public import Silmaril.SSA.SeaOfNodes.Quads.Join.Defs

/-! # Finite occurrence tables and acyclic sequences of quad joins

A table has one column per incoming occurrence, even if two occurrences
use the same block. A choice and at least two occurrences give one split
and join. The returned register bank is the input of the next join.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join.Finite

open RVSDG (PortType Tuple Wires extend)
open Diamond (Ty ValueSort Signature Model Val dataPorts)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)}
variable {args head : List (Ty Data)} {past : List (List (Ty Data))}

/-- Incoming occurrences are identified by their positions in this list. -/
abbrev Table (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) :=
  List (Block Op regs)

/-- Each column is computed in its own predecessor's numbered scope. -/
def Table.incoming (table : Table Op regs) (edge : Fin table.length) :
    Wires (dataPorts regs) (extend [] (Block.producers (table.get edge))) (dataPorts regs) :=
  Block.versions (table.get edge) (initial regs)

/-- Compile one predecessor with the whole final bank as its exit interface. -/
def Table.arm (table : Table Op regs) (edge : Fin table.length) :
    RVSDG.Term (Opcode Op) (dataPorts regs) [] (Block.producers (table.get edge)) (dataPorts regs) :=
  Block.lowerFrom (table.get edge) (initial regs) .jump

/-- A native γ stage has two distinguished occurrences and a finite list of further ones. -/
structure Stage (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) where
  first : Block Op regs
  second : Block Op regs
  more : List (Block Op regs)
  choice : Choice regs (more.length + 2)

def Stage.table (stage : Stage Op regs) : Table Op regs :=
  stage.first :: stage.second :: stage.more

/-- Execute the chosen closed predecessor from the current source bank. -/
def Stage.eval (stage : Stage Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) : Tuple (Val m.value) (dataPorts regs) :=
  Block.eval (stage.table.get (stage.choice.eval bank)) m bank

abbrev Stage.routePorts (stage : Stage Op regs) : List (Ty Data) :=
  .control (stage.more.length + 2) :: dataPorts regs

/-- Wires into the ordered tuple just bound at the end of a prefix. -/
def lastBank (past : List (List (Ty Data))) (head : List (Ty Data)) :
    Wires args (past ++ [head]) head :=
  tabulate head (fun port => .output (Diamond.lastIndex head past) (Diamond.lastPort port past))

/-- Choose an occurrence and pass the current bank alongside its control tag. -/
def Stage.routeNode (stage : Stage Op regs) (current : Wires args past (dataPorts regs)) :
    RVSDG.Node (Opcode Op) args past stage.routePorts :=
  ⟨_, .simple (.route stage.choice), current, Fin.elim0⟩

def Stage.gammaNode (stage : Stage Op regs) (past : List (List (Ty Data))) :
    RVSDG.Node (Opcode Op) args (past ++ [stage.routePorts]) (dataPorts regs) :=
  ⟨_, .gamma stage.more.length, lastBank past stage.routePorts,
    fun i => Block.producers (stage.table.get i)⟩

/-- Acyclic sequences of closed splits and joins over the same register interface. -/
abbrev Plan (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) :=
  List (Stage Op regs)

def Plan.eval (plan : Plan Op regs) (m : Model.{u, v, w} Op)
    (bank : Tuple (Val m.value) (dataPorts regs)) : Tuple (Val m.value) (dataPorts regs) :=
  plan.foldl (fun current stage => stage.eval m current) bank

def Plan.producers : Plan Op regs → List (List (Ty Data))
  | [] => []
  | stage :: rest => stage.routePorts :: dataPorts regs :: Plan.producers rest

/-- Emit one selector and γ per stage. The new current map names the γ result ports. -/
def Plan.lowerFrom : (plan : Plan Op regs) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) →
      RVSDG.Term (Opcode Op) args past plan.producers (dataPorts regs)
  | [], _, current => .ret current
  | stage :: rest, past, current =>
    .bind (stage.routeNode current) (fun i => i.elim0)
      (.bind (stage.gammaNode past) (Table.arm stage.table)
        (Plan.lowerFrom rest (lastBank (past ++ [stage.routePorts]) (dataPorts regs))))

def Plan.lower (plan : Plan Op regs) :
    RVSDG.Graph (Opcode Op) (dataPorts regs) [] plan.producers (dataPorts regs) :=
  (plan.lowerFrom (initial regs)).toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Join.Finite
