module

public import Silmaril.SSA.SeaOfNodes.Quads.Defs

/-! # One ordered quad branch and join

Both predecessors are closed straight-line blocks. A taken edge passes
its complete current register tuple to the join block as typed arguments.
The target keeps arm-local producers in the corresponding RVSDG γ child.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Join

open RVSDG (PortType Port Tuple Origin Wires Locals extend)
open Diamond (Ty ValueSort Signature Model Val dataPorts sortValue Merge Projection Slot)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {args outs : List (Ty Data)} {past : List (List (Ty Data))}

/-- A straight-line block without its terminator. -/
abbrev Block (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) := List (Quad Op regs)

/-- Execute the ordered assignments against the current bank. -/
def Block.eval (block : Block Op regs) (m : Model.{u, v, w} Op)
    (store : Tuple (Val m.value) (dataPorts regs)) : Tuple (Val m.value) (dataPorts regs) :=
  block.foldl (fun state quad => quad.eval m state) store

def Block.producers (block : Block Op regs) : List (List (Ty Data)) :=
  block.map (fun quad => [.value quad.result])

/-- A closed predecessor sends the whole bank. The join block returns one slot. -/
inductive Exit (regs : List (ValueSort Data)) : List (Ty Data) → Type u where
  | jump : Exit regs (dataPorts regs)
  | ret {out : ValueSort Data} (result : Port (dataPorts regs) (.value out)) :
      Exit regs [.value out]

def Exit.select {F : Ty Data → Type w} :
    {outs : List (Ty Data)} → Exit regs outs → Tuple F (dataPorts regs) → Tuple F outs
  | _, .jump, bank => bank
  | _, .ret result, bank => .cons (bank.get result) .nil

def slotIndex : Slot → Fin 2
  | .first => 0
  | .second => 1

def slotAt : Fin 2 → Slot := Fin.cases .first (fun _ => .second)

/-- Select the Region slot for the taken If projection. -/
def selected (merge : Merge) (condition : Bool) : Slot :=
  merge.slot (Projection.ofBool condition)

/-- A finite choice made from the current bank. Leaves name incoming occurrences. -/
inductive Choice (regs : List (ValueSort Data)) (arity : Nat) where
  | take (edge : Fin arity)
  | test (condition : Port (dataPorts regs) (.value .predicate))
      (onTrue onFalse : Choice regs arity)

def Choice.eval {arity : Nat} {value : Data → Type w}
    (bank : Tuple (Val value) (dataPorts regs)) : Choice regs arity → Fin arity
  | .take edge => edge
  | .test condition onTrue onFalse =>
    if (bank.get condition).down then onTrue.eval bank else onFalse.eval bank

/-- Pure quad instructions and the selector that encodes the Region's edge order. -/
inductive Opcode (Op : Signature.{u, v} Data) :
    RVSDG.Dialect.{u, max u v} (ValueSort Data) PEmpty.{u + 1} where
  | pure {ins : List (ValueSort Data)} {out : ValueSort Data} :
      Op ins out → Opcode Op (dataPorts ins) [.value out]
  | select (merge : Merge) : Opcode Op [.value .predicate] [.control 2]
  | route {regs : List (ValueSort Data)} {arity : Nat} (choice : Choice regs arity) :
      Opcode Op (dataPorts regs) (.control arity :: dataPorts regs)

abbrev model (m : Model.{u, v, w} Op) : RVSDG.Model (Opcode Op) where
  value := sortValue m.value
  state := fun impossible => nomatch impossible
  run
    | .pure op, input => .cons (m.run op input) .nil
    | .select merge, .cons condition .nil => .cons ⟨slotIndex (selected merge condition.down)⟩ .nil
    | .route choice, input => .cons ⟨choice.eval input⟩ input

/-- Follow the assignments to obtain the current definition of each register
on this block's outgoing edge. -/
def Block.versions : (block : Block Op regs) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) → Wires args (extend past block.producers) (dataPorts regs)
  | [], _, current => current
  | quad :: rest, _, current => Block.versions rest (rebind current quad.dest)

def Block.lowerFrom : (block : Block Op regs) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) → Exit regs outs →
      RVSDG.Term (Opcode Op) args past block.producers outs
  | [], _, current, exit => .ret (exit.select current)
  | quad :: rest, _, current, exit =>
      .bind (quad.node Opcode.pure current) (fun i => i.elim0)
        (Block.lowerFrom rest (rebind current quad.dest) exit)

/-- The input predicate chooses one of two closed predecessors, then the
join executes in the bank delivered by that predecessor. -/
structure Program (Op : Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  condition : Port (dataPorts regs) (.value .predicate)
  merge : Merge
  predecessor : Slot → Block Op regs
  join : Block Op regs
  result : Port (dataPorts regs) (.value out)

def Program.selectedSlot (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) : Slot :=
  selected p.merge (entry.get p.condition).down

def Program.eval (p : Program Op regs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts regs)) : sortValue m.value out :=
  let current := (p.predecessor (p.selectedSlot m entry)).eval m entry
  (p.join.eval m current).get p.result

/-- Each incoming column is computed from its own arm scope and final version map. -/
def Program.incoming (p : Program Op regs out) (edge : Slot) :
    Wires (dataPorts regs) (extend [] (Block.producers (p.predecessor edge))) (dataPorts regs) :=
  Block.versions (p.predecessor edge) (initial regs)

def Program.arm (p : Program Op regs out) (i : Fin 2) :
    RVSDG.Term (Opcode Op) (dataPorts regs) [] (Block.producers (p.predecessor (slotAt i)))
      (dataPorts regs) :=
  Block.lowerFrom (p.predecessor (slotAt i)) (initial regs) .jump

def Program.selectNode (p : Program Op regs out) :
    RVSDG.Node (Opcode Op) (dataPorts regs) [] [.control 2] :=
  ⟨_, .simple (.select p.merge), .cons (.arg p.condition) .nil, Fin.elim0⟩

def Program.gammaNode (p : Program Op regs out) :
    RVSDG.Node (Opcode Op) (dataPorts regs) [[.control 2]] (dataPorts regs) :=
  ⟨_, .gamma 0, .cons (.output (0 : Fin 1) .head)
    (tabulate _ (fun port => .arg port)),
    fun i => Block.producers (p.predecessor (slotAt i))⟩

/-- The selected child bank is bound once, and all join reads name its ports. -/
def Program.joinWires (regs : List (ValueSort Data)) :
    Wires (dataPorts regs) [[.control 2], dataPorts regs] (dataPorts regs) :=
  tabulate _ (fun port => .output (1 : Fin 2) port)

def Program.lowerTerm (p : Program Op regs out) :
    RVSDG.Term (Opcode Op) (dataPorts regs) []
      ([.control 2] :: dataPorts regs :: p.join.producers) [.value out] :=
  .bind p.selectNode (fun i => i.elim0)
    (.bind p.gammaNode p.arm (p.join.lowerFrom (Program.joinWires regs) (.ret p.result)))

def Program.lower (p : Program Op regs out) :
    RVSDG.Graph (Opcode Op) (dataPorts regs) []
      ([.control 2] :: dataPorts regs :: p.join.producers) [.value out] :=
  p.lowerTerm.toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Join
