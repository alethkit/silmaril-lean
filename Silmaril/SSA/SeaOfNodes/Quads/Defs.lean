module

public import Silmaril.SSA.SeaOfNodes.Diamond.Defs

/-! # Ordered quads with typed mutable registers

A register is a typed slot in a fixed bank, supplied in full at entry.
Each instruction reads all operands before overwriting one slot. Lowering
keeps the current origin of each slot and emits ordinary RVSDG bindings.
-/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads

open RVSDG (PortType Port Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- Each assignment names a destination and an ordered tuple of source registers. -/
inductive Code (Op : Signature.{u, v} Data) (regs : List (ValueSort Data))
    (out : ValueSort Data) where
  | ret (result : Port (dataPorts regs) (.value out))
  | assign {ins : List (ValueSort Data)} {result : ValueSort Data}
      (dest : Port (dataPorts regs) (.value result)) (op : Op ins result)
      (operands : Tuple (Port (dataPorts regs)) (dataPorts ins)) (next : Code Op regs out)

/-- Write one typed slot in a register bank. -/
def write {T : Type u} {F : T → Type w} {t : T} :
    {ts : List T} → Port ts t → F t → Tuple F ts → Tuple F ts
  | _, .head, value, .cons _ tail => .cons value tail
  | _, .tail dest, value, .cons old tail => .cons old (write dest value tail)

/-- One assignment shared by the straight-line and branch/join profiles. -/
structure Quad (Op : Signature.{u, v} Data) (regs : List (ValueSort Data)) where
  ins : List (ValueSort Data)
  result : ValueSort Data
  dest : Port (dataPorts regs) (.value result)
  op : Op ins result
  operands : Tuple (Port (dataPorts regs)) (dataPorts ins)

/-- Read all operands before updating the destination. -/
def Quad.eval (quad : Quad Op regs) (m : Model.{u, v, w} Op)
    (store : Tuple (Val m.value) (dataPorts regs)) : Tuple (Val m.value) (dataPorts regs) :=
  write quad.dest (m.run quad.op (quad.operands.map (fun _ source => store.get source))) store

/-- Resolve the operand wires in the version map before this assignment. -/
def Quad.inputWires (quad : Quad Op regs) {args : List (Ty Data)} {past : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs)) : Wires args past (dataPorts quad.ins) :=
  quad.operands.map (fun _ source => current.get source)

/-- Emit the assignment as one ordinary RVSDG producer in a dialect with these pure opcodes. -/
def Quad.node (quad : Quad Op regs)
    {D : RVSDG.Dialect (ValueSort Data) PEmpty.{u + 1}}
    (emit : ∀ {ins result}, Op ins result → D (dataPorts ins) [.value result])
    {args : List (Ty Data)} {past : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs)) :
    RVSDG.Node D args past [.value quad.result] :=
  ⟨_, .simple (emit quad.op), quad.inputWires current, Fin.elim0⟩

/-- The zero-based slot, allowing comparison between differently typed ports. -/
def slot {T : Type u} {ts : List T} {t : T} : Port ts t → Nat
  | .head => 0
  | .tail port => slot port + 1

/-- Source execution uses a mutable bank and reports the returned value. -/
def Code.eval (m : Model.{u, v, w} Op) :
    Code Op regs out → Tuple (Val m.value) (dataPorts regs) → sortValue m.value out
  | .ret result, store => store.get result
  | .assign dest op operands next, store => next.eval m ((Quad.mk _ _ dest op operands).eval m store)

/-- Exactly one producer result is appended for each assignment, in source order. -/
def Code.producers : Code Op regs out → List (List (Ty Data))
  | .ret _ => []
  | .assign (result := result) _ _ _ next => [.value result] :: next.producers

/-- Keep the same origin when appending a later producer. -/
def keep {args added : List (Ty Data)} {past : List (List (Ty Data))} {t : Ty Data} :
    Origin args past t → Origin args (past ++ [added]) t
  | .arg p => .arg p
  | .output i p =>
      .output ⟨i.val, by simpa using Nat.lt_succ_of_lt i.isLt⟩
        (by
          change Port (past ++ [added])[i.val] t
          rw [List.getElem_append_left i.isLt]
          exact p)

/-- Update the destination to the new producer's sole output. All other
registers keep their origins in the extended prefix. -/
def rebind {args : List (Ty Data)} {past : List (List (Ty Data))}
    (current : Wires args past (dataPorts regs)) {result : ValueSort Data}
    (dest : Port (dataPorts regs) (.value result)) :
    Wires args (past ++ [[.value result]]) (dataPorts regs) :=
  write dest (.output (Diamond.lastIndex [.value result] past)
    (Diamond.lastPort .head past)) (current.map (fun _ origin => keep origin))

/-- Gather the value for each typed slot in order. -/
def tabulate {T : Type u} {F : T → Type w} :
    (ts : List T) → (∀ {t}, Port ts t → F t) → Tuple F ts
  | [], _ => .nil
  | _ :: tail, f => .cons (f .head) (tabulate tail (fun p => f (.tail p)))

/-- All entry register versions name their corresponding input slots. -/
def initial (regs : List (ValueSort Data)) : Wires (dataPorts regs) [] (dataPorts regs) :=
  tabulate _ (fun port => .arg port)

/-- Emit ordinary RVSDG bindings. The operands use the old map, and the
continuation alone receives the updated map. -/
def Code.lowerFrom {args : List (Ty Data)} :
    (code : Code Op regs out) → {past : List (List (Ty Data))} →
    Wires args past (dataPorts regs) →
      RVSDG.Term (Diamond.Opcode Op) args past code.producers [.value out]
  | .ret result, _, current => .ret (.cons (current.get result) .nil)
  | .assign dest op operands next, _, current =>
      .bind ((Quad.mk _ _ dest op operands).node Diamond.Opcode.pure current)
        (fun j => j.elim0) (next.lowerFrom (rebind current dest))

/-- The numbered graph uses existing RVSDG origins and result ports. -/
def Code.lower (code : Code Op regs out) :
    RVSDG.Graph (Diamond.Opcode Op) (dataPorts regs) [] code.producers [.value out] :=
  (code.lowerFrom (initial regs)).toGraph

end Silmaril.SSA.SeaOfNodes.Quads
