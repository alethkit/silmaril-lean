module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.MLIR.Institution.Defs

/-! # A scoped MLIR dialect for pure acyclic RVSDG

This project dialect uses the MLIR institution's isolated single-block syntax.
Local wires are resolved into expressions, and each γ arm gets a fresh
parameter context. The source has no state sorts.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph

open CategoryTheory
open Silmaril.MLIR.Institution (Block OpArity Profile Signature)

abbrev Ty (V : Type) := PortType V PEmpty
abbrev Source (V : Type) := Institution.Signature.{0, 0} V PEmpty

variable {V : Type} {P : Source V}

/-- Region slots and output positions retain their source ordering. -/
abbrev arity (ins outs : Ports (Ty V)) (count : Nat) (entry exit : Ports (Ty V)) :
    OpArity true :=
  ⟨ins.length, outs.length, ⟨count, fun _ => ⟨entry.length, exit.length⟩⟩⟩

abbrev profile (ins outs : Ports (Ty V)) (count : Nat) (entry exit : Ports (Ty V)) :
    Profile (arity ins outs count entry exit) (Ty V) :=
  ⟨ins.get, outs.get, fun _ => entry.get, fun _ => exit.get⟩

/-- `rvsdg.simple` carries the typed primitive opcode. `rvsdg.gamma` has one
isolated region per selector value, each with the same parameter and yield profiles. -/
inductive Op (P : Source V) : {a : OpArity true} → Profile a (Ty V) → Type where
  | simple {ins outs : Ports (Ty V)} (op : P.op ins outs) : Op P (profile ins outs 0 [] [])
  | gamma (entry exit : Ports (Ty V)) (extra : Nat) :
      Op P (profile (.control (extra + 2) :: entry) exit (extra + 2) entry exit)

def Op.name {a : OpArity true} {p : Profile a (Ty V)} : Op P p → String
  | .simple _ => "rvsdg.simple"
  | .gamma .. => "rvsdg.gamma"

abbrev signature (P : Source V) : Signature true := ⟨Ty V, Op P⟩

/-- Relabel the primitive payload in a typed symbol. γ keeps its region slots
and every symbol retains its full port profile. -/
def Op.map {Q : Source V} (h : P ⟶ Q) {a : OpArity true} {p : Profile a (Ty V)} :
    Op P p → Op Q p
  | .simple op => .simple (Institution.Signature.opcodeMap h op)
  | .gamma entry exit extra => .gamma entry exit extra

/-- An RVSDG signature morphism induces a scoped MLIR signature morphism. -/
def mapSignature {Q : Source V} (h : P ⟶ Q) : signature P ⟶ signature Q where
  sort := id
  symbol := Op.map h

/-- Read an ordered RVSDG tuple as a finite MLIR assignment. -/
def toAssignment {F : Ty V → Type} : {ts : Ports (Ty V)} →
    Tuple F ts → (i : Fin ts.length) → F (ts.get i)
  | [], .nil, i => i.elim0
  | _ :: _, .cons x xs, i => Fin.cases (motive := fun j => F (List.get (_ :: _) j))
      x (toAssignment xs) i

/-- Assemble an RVSDG tuple from the corresponding ordered MLIR assignment. -/
def ofAssignment {F : Ty V → Type} : (ts : Ports (Ty V)) →
    ((i : Fin ts.length) → F (ts.get i)) → Tuple F ts
  | [], _ => .nil
  | _ :: ts, env => .cons (env 0) (ofAssignment ts (fun i => env i.succ))

/-- Interpret the project dialect with total primitives. A γ applies the selected
body to the operand tuple after dropping the leading selector. -/
def model (m : Model.{0, 0, 0} P.op) : Silmaril.MLIR.Institution.Model (signature P) where
  carrier := m.Val
  op
    | .simple op, args, _ => toAssignment (m.run op (ofAssignment _ args))
    | .gamma _ _ _, args, bodies => bodies (args 0).down (fun i => args i.succ)

abbrev Expr (P : Source V) {n : Nat} (Γ : Fin n → Ty V) :=
  Silmaril.MLIR.Institution.Term (signature P) Γ

/-- Apply an operation at every result slot. The MLIR institution represents a
block's ordered yield as a tuple of expressions. -/
def emit {n : Nat} {Γ : Fin n → Ty V} {ins outs : Ports (Ty V)}
    (shape : Shape P.op ins outs)
    (operands : Tuple (Expr P Γ) ins)
    (bodies : (r : Fin shape.regionCount) →
      Block (signature P) shape.entry.get shape.exit.get) :
    Tuple (Expr P Γ) outs :=
  match shape with
  | .simple op => ofAssignment outs (fun i =>
      .app (S := signature P) (p := profile ins outs 0 [] [])
        (Op.simple op) (toAssignment operands) (fun r => r.elim0) i)
  | @Shape.gamma _ _ _ entry exit extra => ofAssignment exit (fun i =>
      .app (S := signature P)
        (p := profile (.control (extra + 2) :: entry) exit (extra + 2) entry exit)
        (Op.gamma entry exit extra) (toAssignment operands) bodies i)

/-- Lower a region in a given environment of operand expressions. Each nested
region starts with its own variables and no inherited local definitions. -/
def lowerTerm : {n : Nat} → {Γ : Fin n → Ty V} → {args outs : Ports (Ty V)} →
    {past sigs : List (Ports (Ty V))} →
    Tuple (Expr P Γ) args → Locals (Expr P Γ) past →
    Term P.op args past sigs outs → Tuple (Expr P Γ) outs
  | _, _, _, _, _, _, args, locals, .ret results => results.read args locals
  | _, _, _, _, _, _, args, locals, .bind node children rest =>
    let result := emit node.shape (node.inputs.read args locals)
      (fun r => toAssignment (lowerTerm (past := []) (ofAssignment _ .var) PUnit.unit (children r)))
    lowerTerm args (locals.snoc result) rest

/-- Lower a whole numbered RVSDG region to an isolated, typed MLIR block. -/
def lower {args outs : Ports (Ty V)} {sigs : List (Ports (Ty V))}
    (g : RVSDG.Graph P.op args [] sigs outs) : Block (signature P) args.get outs.get :=
  toAssignment (lowerTerm (past := []) (ofAssignment _ .var) PUnit.unit g.toTerm)

end Silmaril.SSA.RVSDG.MLIR.Graph
