module

public import Silmaril.SSA.MLIR.Institution.Arith.Defs

public section

namespace Silmaril.Proofs.MLIR.Institution.Arith

open Silmaril.MLIR.Institution
open Silmaril.MLIR.Institution.Arith
open Silmaril.MLIR.Arith (Width Var Env Rhs)

variable {n : Nat} {Δ : Fin n → Width} {Γ : List Width} {w : Width}

private theorem rhsTerm_denote (rhs : Rhs Γ w) (vars : ∀ {v}, Var Γ v → Term signature Δ v)
    (env : Env Γ) (η : Assignment model.carrier Δ)
    (agree : ∀ {v} (x : Var Γ v), (vars x).denote model η = env.get x) :
    (rhsTerm vars rhs).denote model η = rhs.denote env := by
  cases rhs with
  | constant value => rfl
  | binary op x y =>
      change op.denote ((vars x).denote model η) ((vars y).denote model η) =
        op.denote (env.get x) (env.get y)
      rw [agree x, agree y]

private theorem blockTerm_denote (block : Silmaril.MLIR.Arith.Block Γ w) :
    ∀ {n : Nat} {Δ : Fin n → Width} (vars : ∀ {v}, Var Γ v → Term signature Δ v)
      (env : Env Γ) (η : Assignment model.carrier Δ),
      (∀ {v} (x : Var Γ v), (vars x).denote model η = env.get x) →
      (blockTerm vars block).denote model η = block.denote env := by
  induction block with
  | yield x =>
      intro _ _ vars env η agree
      exact agree x
  | letOp rhs rest ih =>
      intro _ _ vars env η agree
      simp only [blockTerm, Silmaril.MLIR.Arith.Block.denote]
      apply ih
      intro v x
      cases x with
      | here => exact rhsTerm_denote rhs vars env η agree
      | there x => exact agree x
  | letRegion arg body rest ihBody ihRest =>
      intro _ _ vars env η agree
      simp only [blockTerm, Silmaril.MLIR.Arith.Block.denote]
      apply ihRest
      intro v x
      cases x with
      | here =>
          change (blockTerm regionVar body).denote model (fun _ => (vars arg).denote model η) =
            body.denote (.cons (env.get arg) .nil)
          apply ihBody
          intro v x
          cases x with
          | here => exact agree arg
          | there x => cases x
      | there x => exact agree x

private theorem denote_transport {s t : Width} (h : s = t) (value : Term signature Δ s)
    (η : Assignment model.carrier Δ) :
    (h ▸ value : Term signature Δ t).denote model η =
      (h ▸ value.denote model η : BitVec t.val) := by
  cases h
  rfl

private theorem assignment_slot (x : Var Γ w) (env : Env Γ) :
    (slot_type x ▸ assignment env (slot x) : BitVec w.val) = env.get x := by
  induction x with
  | here => cases env; rfl
  | there x ih => cases env; exact ih _

theorem translate_denote (block : Silmaril.MLIR.Arith.Block Γ w) (env : Env Γ) :
    (translate block).denote model (assignment env) = block.denote env := by
  apply blockTerm_denote
  intro v x
  rw [varTerm, denote_transport]
  exact assignment_slot x env

end Silmaril.Proofs.MLIR.Institution.Arith
