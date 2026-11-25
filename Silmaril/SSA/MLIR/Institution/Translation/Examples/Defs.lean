module

public import Silmaril.SSA.MLIR.Institution.Translation.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Defs

/-! Lower a dialect extension with a dedicated doubling operation to scalar arithmetic. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Translation.Examples

open Silmaril.MLIR.Arith (Width)

inductive Op : {arity : OpArity true} → Profile arity Width → Type where
  | core {a : OpArity true} {p : Profile a Width} (op : Arith.Op p) : Op p
  | double (w : Width) : Op (Arith.scalarProfile 1 w)

abbrev signature : Signature true := ⟨Width, Op⟩

/-- The source model interprets its primitive doubling by modular addition. -/
def model : Model signature where
  carrier := Arith.model.carrier
  op
    | .core op, args, bodies => Arith.model.op op args bodies
    | .double w, args, _ => fun _ => BitVec.add (args 0 : BitVec w.val) (args 0 : BitVec w.val)

/-- The target block materializes two at the requested width and multiplies the input. -/
def doubleBlock (w : Width) :
    Block Arith.signature (fun _ : Fin 1 => w) (fun _ : Fin 1 => w) :=
  fun _ =>
    let two := Term.app (S := Arith.signature) (p := Arith.scalarProfile 0 w)
      (.constant w (BitVec.ofNat w.val 2)) (fun i => Fin.elim0 i) (fun r => Fin.elim0 r) 0
    Term.app (S := Arith.signature) (p := Arith.scalarProfile 2 w) (.binary w .muli)
      (Fin.cases (.var 0) (fun _ => two)) (fun r => Fin.elim0 r) 0

/-- Core symbols retain their interfaces, including the isolated application operation. -/
def lower : Interpretation signature Arith.signature where
  sort w := w
  image
    | .core op => .forward op
    | .double w => .expand rfl (doubleBlock w)

/-- Apply a region that doubles its own parameter. The outer argument is in the second slot. -/
def scopedDouble (a w : Width) : Term signature (Fin.cases a (fun _ : Fin 1 => w)) w :=
  let body := Term.app (S := signature) (Γ := fun _ : Fin 1 => w) (p := Arith.scalarProfile 1 w)
    (.double w) (fun _ => .var 0) (fun r => Fin.elim0 r) 0
  Term.app (S := signature) (p := Arith.applyProfile w w) (.core (.apply w w))
    (fun _ => .var 1) (fun _ _ => body) 0

end Silmaril.MLIR.Institution.Translation.Examples
