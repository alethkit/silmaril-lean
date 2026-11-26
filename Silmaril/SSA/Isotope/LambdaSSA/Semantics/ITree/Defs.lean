module

public import Silmaril.SSA.Isotope.LambdaSSA.Defs
public import Silmaril.Semantics.ITree.Thms

/-! # Weak interaction trees for positional LambdaSSA -/

@[expose] public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction

open Silmaril.Elgot.ITree

/-- A primitive request records the instruction and its evaluated operand.
The environment supplies one runtime value as the reply. -/
inductive Event (Φ α : Type u) : Type u → Type u
  | call (opcode : Φ) (arg : Value α) : Event Φ α (Value α)

abbrev Primitive (F : Type w → Type w) (Φ : Type v) (α : Type u) :=
  Φ → Value α → Tree F (Value α)

/-- The free interpretation exposes every primitive call, with one continuation
for each reply. Runtime replies are unrefined values, as in the erased syntax. -/
def request {Φ α : Type u} : Primitive (Event Φ α) Φ α :=
  fun op arg => vis (.call op arg) pure

abbrev Transfer (α : Type u) := Nat × Value α
abbrev BlockInput (α : Type u) (arity : Nat) := Fin arity × Value α

variable {F : Type w → Type w} {Φ : Type v} {α : Type u}

/-- Interpret the erased term in evaluation order. A shape mismatch has no
result in this observation model. -/
def term (instr : Primitive F Φ α) (env : Env α) : Tm Φ → Tree F (Value α)
  | .var i => pure (env i)
  | .op op a => term instr env a >>= instr op
  | .let₁ a b => term instr env a >>= fun v => term instr (extend env v) b
  | .pair a b => term instr env a >>= fun x => term instr env b >>= fun y => pure (.pair x y)
  | .unit => pure .unit
  | .let₂ a b => term instr env a >>= fun
    | .pair x y => term instr (extend (extend env x) y) b
    | _ => diverge
  | .inl a => term instr env a >>= fun v => pure (.inl v)
  | .inr a => term instr env a >>= fun v => pure (.inr v)
  | .case a l r => term instr env a >>= fun
    | .inl v => term instr (extend env v) l
    | .inr v => term instr (extend env v) r
    | _ => diverge
  | .abort a => term instr env a >>= fun _ => diverge

/-- Local CFG labels precede outward labels. Outward indices are relative to
the enclosing interface. -/
def splitTransfer (arity : Nat) (p : Transfer α) : Transfer α ⊕ BlockInput α arity :=
  if h : p.1 < arity then .inr (⟨p.1, h⟩, p.2) else .inl (p.1 - arity, p.2)

/-- Interpret a region, using the actual weak ITree iterator at each CFG.
Every block sees its own payload above the environment at the CFG boundary. -/
noncomputable def region (instr : Primitive F Φ α) (env : Env α) :
    Region Φ → Tree F (Transfer α)
  | .br i a => term instr env a >>= fun v => pure (i, v)
  | .let₁ a b => term instr env a >>= fun v => region instr (extend env v) b
  | .let₂ a b => term instr env a >>= fun
    | .pair x y => region instr (extend (extend env x) y) b
    | _ => diverge
  | .case a l r => term instr env a >>= fun
    | .inl v => region instr (extend env v) l
    | .inr v => region instr (extend env v) r
    | _ => diverge
  | .cfg e arity blocks =>
    let step := fun p : BlockInput α arity =>
      region instr (extend env p.2) (blocks p.1) >>= fun out => pure (splitTransfer arity out)
    region instr env e >>= fun out => Sum.elim pure (iterate step) (splitTransfer arity out)

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction
