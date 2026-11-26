module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.RVSDG.Theta.Defs

/-! # One PEG loop with two typed carried slots, as a whole-region RVSDG θ -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge.Theta

open RVSDG (Tuple Wires)

variable {Data : Type} {P : InstructionSet.{0,0} Data} {a b : Ty Data}

/-- The two updates and the exit test read the same ordered current tuple. -/
structure Loop (P : InstructionSet.{0,0} Data) (a b : Ty Data) where
  stop : P [a, b] .bool
  nextLeft : P [a, b] a
  nextRight : P [a, b] b

def sorts (a b : Ty Data) : Fin 10 → Ty Data
  | ⟨0, _⟩ | ⟨2, _⟩ | ⟨6, _⟩ | ⟨8, _⟩ => a
  | ⟨4, _⟩ => .bool
  | ⟨5, _⟩ => .count
  | _ => b

def carriedRefs (a b : Ty Data) : Tuple (Ref (sorts a b)) [a, b] :=
  .cons ⟨2, rfl⟩ (.cons ⟨3, rfl⟩ .nil)

/-- The admitted PEG table. Both eval roots sample the carried streams at
the one shared pass. The initial values are the two parameters. -/
def Loop.peg (loop : Loop P a b) : Graph P [a, b] [a, b] 10 1 where
  forest := ⟨fun _ => none⟩
  sort := sorts a b
  node
    | ⟨0, _⟩ => .ofLabel (.param .head) .nil
    | ⟨1, _⟩ => .ofLabel (.param (.tail .head)) .nil
    | ⟨2, _⟩ => .ofLabel (.theta 0) (.cons ⟨0, rfl⟩ (.cons ⟨6, rfl⟩ .nil))
    | ⟨3, _⟩ => .ofLabel (.theta 0) (.cons ⟨1, rfl⟩ (.cons ⟨7, rfl⟩ .nil))
    | ⟨4, _⟩ => .ofLabel (.op loop.stop) (carriedRefs a b)
    | ⟨5, _⟩ => .ofLabel (.pass 0) (.cons ⟨4, rfl⟩ .nil)
    | ⟨6, _⟩ => .ofLabel (.op loop.nextLeft) (carriedRefs a b)
    | ⟨7, _⟩ => .ofLabel (.op loop.nextRight) (carriedRefs a b)
    | ⟨8, _⟩ => .ofLabel (.eval 0) (.cons ⟨2, rfl⟩ (.cons ⟨5, rfl⟩ .nil))
    | ⟨9, _⟩ => .ofLabel (.eval 0) (.cons ⟨3, rfl⟩ (.cons ⟨5, rfl⟩ .nil))
    | ⟨i + 10, h⟩ => False.elim (by omega)
  roots := .cons ⟨8, rfl⟩ (.cons ⟨9, rfl⟩ .nil)

/-- Sample requests decrease the first phase, feedback decreases the counter,
and the remaining ordinary/initial requests decrease the last phase. -/
def rank : DemandRank 10 1 :=
  [.phase (fun i => match i.val with
    | 8 | 9 => 2
    | 5 => 1
    | _ => 0),
   .counter 0,
   .phase (fun i => match i.val with
    | 4 | 6 | 7 => 2
    | 2 | 3 => 1
    | _ => 0)]

abbrev Carried (a b : Ty Data) := valuePorts [a, b]

inductive Opcode (P : InstructionSet.{0,0} Data) (a b : Ty Data) :
    RVSDG.Dialect (Ty Data) PUnit
  | test (stop : P [a, b] .bool) : Opcode P a b (Carried a b) [.control 2]
  | update {t : Ty Data} (op : P [a, b] t) : Opcode P a b (Carried a b) (valuePorts [t])

def model (m : TotalModel P) (a b : Ty Data) : RVSDG.Model (Opcode P a b) where
  value := m.toPEG.Value
  state _ := PEmpty
  run
    | .test test, input => .cons ⟨if (m.run test (fromPorts [a, b] input)).down then 0 else 1⟩ .nil
    | .update op, input => .cons (m.run op (fromPorts [a, b] input)) .nil

abbrev encodeCarried (m : TotalModel P) (xs : Tuple m.toPEG.Value [a, b]) :
    Tuple (model m a b).Val (Carried a b) :=
  toPorts (F := (model m a b).Val) xs

def Loop.advance (loop : Loop P a b) (m : TotalModel P) (input : Tuple m.toPEG.Value [a, b]) :
    Tuple m.toPEG.Value [a, b] :=
  .cons (m.run loop.nextLeft input) (.cons (m.run loop.nextRight input) .nil)

def Loop.exits (loop : Loop P a b) (m : TotalModel P) (input : Tuple m.toPEG.Value [a, b]) : Bool :=
  (m.run loop.stop input).down

/-- Input to body activation k, where the first activation has index zero. -/
def Loop.stateAt (loop : Loop P a b) (m : TotalModel P) :
    Nat → Tuple m.toPEG.Value [a, b] → Tuple m.toPEG.Value [a, b]
  | 0, input => input
  | k + 1, input => loop.stateAt m k (loop.advance m input)

def Loop.FirstExit (loop : Loop P a b) (m : TotalModel P) (input : Tuple m.toPEG.Value [a, b])
    (k : Nat) : Prop :=
  loop.exits m (loop.stateAt m k input) = true ∧
    ∀ j < k, loop.exits m (loop.stateAt m j input) = false

namespace Compiler

def args (a b : Ty Data) (past : List (List (ValuePort Data))) :
    Wires (Carried a b) past (Carried a b) :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

def exitArm (P : InstructionSet.{0,0} Data) (a b : Ty Data) :
    RVSDG.Term (Opcode P a b) (Carried a b) [] [] (Carried a b) :=
  .ret (args a b [])

def updateNode (past : List (List (ValuePort Data))) {t : Ty Data} (op : P [a, b] t) :
    RVSDG.Node (Opcode P a b) (Carried a b) past (valuePorts [t]) :=
  ⟨_, .simple (.update op), args a b past, Fin.elim0⟩

/-- Both vertices read the arm arguments. The second update cannot see the
first one's output. -/
def continueArm (loop : Loop P a b) :
    RVSDG.Term (Opcode P a b) (Carried a b) [] [valuePorts [a], valuePorts [b]] (Carried a b) :=
  .bind (updateNode [] loop.nextLeft) (fun j => j.elim0)
    (.bind (updateNode [valuePorts [a]] loop.nextRight) (fun j => j.elim0)
      (.ret (.cons (.output ⟨0, Nat.zero_lt_succ 1⟩ .head) (.cons (.output ⟨1, Nat.lt_succ_self 1⟩ .head) .nil))))

def testNode (loop : Loop P a b) :
    RVSDG.Node (Opcode P a b) (Carried a b) [] [.control 2] :=
  ⟨_, .simple (.test loop.stop), args a b [], Fin.elim0⟩

def selectNode (P : InstructionSet.{0,0} Data) (a b : Ty Data) :
    RVSDG.Node (Opcode P a b) (Carried a b) [[.control 2]] (Carried a b) :=
  ⟨_, .gamma 0, .cons (.output ⟨0, Nat.zero_lt_succ 0⟩ .head) (args a b [[.control 2]]),
    Fin.cases [] (fun _ => [valuePorts [a], valuePorts [b]])⟩

def selectedArm (loop : Loop P a b) (j : Fin 2) :
    RVSDG.Term (Opcode P a b) (Carried a b) [] ((selectNode P a b).childSigs j) (Carried a b) :=
  Fin.cases (motive := fun i => RVSDG.Term (Opcode P a b) (Carried a b) []
    ((selectNode P a b).childSigs i) (Carried a b)) (exitArm P a b) (fun _ => continueArm loop) j

end Compiler

/-- Test the current tuple, route the unchanged tuple through arm zero on
exit, or execute the two updates in arm one and feed them back. -/
def Loop.toThetaTerm (loop : Loop P a b) :
    RVSDG.Theta.Term (Opcode P a b) (Carried a b) [[.control 2], Carried a b] :=
  ⟨.bind (Compiler.testNode loop) (fun j => j.elim0)
    (.bind (Compiler.selectNode P a b)
      (Compiler.selectedArm loop)
      (.ret (.cons (.output ⟨0, Nat.zero_lt_succ 1⟩ .head) (.cons (.output ⟨1, Nat.lt_succ_self 1⟩ .head)
        (.cons (.output ⟨1, Nat.lt_succ_self 1⟩ (.tail .head)) .nil)))))⟩

def Loop.toTheta (loop : Loop P a b) :
    RVSDG.Theta.Graph (Opcode P a b) (Carried a b) [[.control 2], Carried a b] :=
  loop.toThetaTerm.toGraph

/-- Syntactic evidence for using the adapter on an existing PEG table. -/
structure Form (g : Graph P [a, b] [a, b] 10 1) where
  loop : Loop P a b
  table : g = loop.peg

def compile {g : Graph P [a, b] [a, b] 10 1} (form : Form g) :
    RVSDG.Theta.Graph (Opcode P a b) (Carried a b) [[.control 2], Carried a b] :=
  form.loop.toTheta

end Silmaril.SSA.PEG.Bridge.Theta
