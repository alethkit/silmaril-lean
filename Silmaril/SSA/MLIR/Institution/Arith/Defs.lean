module

public import Silmaril.SSA.MLIR.Institution.Defs
public import Silmaril.SSA.MLIR.Arith.Defs

/-! Interpret the scalar arithmetic SSA blocks in the isolated-region institution. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Arith

open Silmaril.MLIR.Arith (Width Var Env BinOp Rhs)

/-- A scalar operation with operands of the same width and no regions. -/
abbrev scalarProfile (n : Nat) (w : Width) :
    Profile (⟨n, 1, ⟨0, Fin.elim0⟩⟩ : OpArity true) Width where
  operand _ := w
  result _ := w
  param := fun r => Fin.elim0 r
  yield := fun r => Fin.elim0 r

/-- Apply one isolated region to the operation's sole operand. -/
abbrev applyProfile (a w : Width) :
    Profile (⟨1, 1, ⟨1, fun _ => ⟨1, 1⟩⟩⟩ : OpArity true) Width where
  operand _ := a
  result _ := w
  param _ _ := a
  yield _ _ := w

inductive Op : {arity : OpArity true} → Profile arity Width → Type where
  | constant (w : Width) (value : BitVec w.val) : Op (scalarProfile 0 w)
  | binary (w : Width) (op : BinOp) : Op (scalarProfile 2 w)
  | apply (a w : Width) : Op (applyProfile a w)

abbrev signature : Signature true := ⟨Width, Op⟩

def model : Model signature where
  carrier w := BitVec w.val
  op
    | .constant _ value, _, _ => fun _ => value
    | .binary _ op, args, _ => fun _ => op.denote (args 0) (args 1)
    | .apply .., args, bodies => bodies 0 (fun _ => args 0)

variable {n : Nat} {Δ : Fin n → Width} {Γ : List Width} {w a : Width}

/-- Interpret the single argument of an isolated arithmetic block. -/
def regionVar : Var [a] w → Term signature (fun _ : Fin 1 => a) w
  | .here => .var 0

/-- Translate an arithmetic primitive using the current interpretation of its SSA operands. -/
def rhsTerm (vars : ∀ {v}, Var Γ v → Term signature Δ v) : Rhs Γ w → Term signature Δ w
  | .constant value => Term.app (S := signature) (Γ := Δ) (p := scalarProfile 0 w)
      (Op.constant w value) (fun i => Fin.elim0 i) (fun r => Fin.elim0 r) 0
  | .binary op x y => Term.app (S := signature) (Γ := Δ) (p := scalarProfile 2 w) (Op.binary w op)
      (Fin.cases (vars x) (fun _ => vars y)) (fun r => Fin.elim0 r) 0

/-- Extend the expression assignment with the term for a freshly defined SSA value. -/
def extendVars (value : Term signature Δ a) (vars : ∀ {v}, Var Γ v → Term signature Δ v) :
    ∀ {v}, Var (a :: Γ) v → Term signature Δ v
  | _, .here => value
  | _, .there x => vars x

/-- Inline a pure arithmetic block into the expression syntax. An SSA let extends the
interpretation of local variables. An isolated body starts with its own parameter. -/
def blockTerm : {n : Nat} → {Δ : Fin n → Width} → {Γ : List Width} → {w : Width} →
    (∀ {v}, Var Γ v → Term signature Δ v) → Silmaril.MLIR.Arith.Block Γ w → Term signature Δ w
  | _, _, _, _, vars, .yield x => vars x
  | _, _, _, _, vars, .letOp rhs rest =>
      blockTerm (extendVars (rhsTerm vars rhs) vars) rest
  | _, Δ, _, _, vars, .letRegion (a := a) (v := v) arg body rest =>
      let value := Term.app (S := signature) (Γ := Δ) (p := applyProfile a v)
        (Op.apply a v) (fun _ => vars arg)
        (fun _ _ => blockTerm regionVar body) 0
      blockTerm (extendVars value vars) rest

/-- The finite slot corresponding to an arithmetic SSA variable. -/
def slot : {Γ : List Width} → {w : Width} → Var Γ w → Fin Γ.length
  | _, _, .here => 0
  | _, _, .there x => (slot x).succ

theorem slot_type (x : Var Γ w) : Γ.get (slot x) = w := by
  induction x with
  | here => rfl
  | there x ih => exact ih

/-- Interpret an open arithmetic variable in the same ordered input context. -/
def varTerm (x : Var Γ w) : Term signature Γ.get w :=
  slot_type x ▸ .var (slot x)

/-- Interpret an open arithmetic block in the institution. -/
def translate (block : Silmaril.MLIR.Arith.Block Γ w) : Term signature Γ.get w :=
  blockTerm varTerm block

/-- The same arithmetic input assignment, indexed by its ordered slots. -/
def assignment : {Γ : List Width} → Env Γ → Assignment model.carrier Γ.get
  | _, .nil => fun i => Fin.elim0 i
  | _, .cons value tail => Fin.cases value (assignment tail)

end Silmaril.MLIR.Institution.Arith
