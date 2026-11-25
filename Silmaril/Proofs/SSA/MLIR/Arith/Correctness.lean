module

public import Silmaril.SSA.MLIR.Arith.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Thms

/-! Typing and exact finite evaluation for the arithmetic lowering. -/

public section

namespace Silmaril.Proofs.MLIR.Arith

open Silmaril.MLIR.Arith
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Width} {w : Width}

private theorem var_lookup (x : Var Γ w) (tail : List (Ty Width)) :
    Isotope.LambdaSSA.At (Γ.map Ty.base ++ tail) x.index (.base w) := by
  induction x with
  | here => rfl
  | there x ih => exact ih

private theorem rhs_hasType (rhs : Rhs Γ w) (tail : List (Ty Width)) :
    Tm.HasType (Γ.map Ty.base ++ tail) rhs.toLambdaSSA (.base w) := by
  cases rhs with
  | constant => exact .op .unit
  | binary _ x y =>
      exact .op (.pair (.var (var_lookup x tail)) (.var (var_lookup y tail)))

private theorem term_hasType (block : MLIR.Arith.Block Γ w) (tail : List (Ty Width)) :
    Tm.HasType (Γ.map Ty.base ++ tail) block.toTerm (.base w) := by
  induction block generalizing tail with
  | yield x => exact .var (var_lookup x tail)
  | letOp rhs _ ih => exact .let₁ (rhs_hasType rhs tail) (ih tail)
  | letRegion arg _ _ bodyIH restIH =>
      exact .let₁ (.let₁ (.var (var_lookup arg tail)) (bodyIH _))
        (restIH tail)

theorem toLambdaSSA_hasType (block : MLIR.Arith.Block Γ w) :
    Region.HasType (Γ.map Ty.base) block.toLambdaSSA [.base w] :=
  .br rfl (by simpa only [List.append_nil] using term_hasType block [])

private theorem env_lookup (x : Var Γ w) (env : Env Γ) (tail : Semantics.Env Atom) :
    env.toLambdaSSA tail x.index = word (env.get x) := by
  induction x with
  | here => cases env; rfl
  | there x ih => cases env; exact ih _

private theorem rhs_eval (rhs : Rhs Γ w) (env : Env Γ) (tail : Semantics.Env Atom) :
    Semantics.Tm.Eval instr (env.toLambdaSSA tail) rhs.toLambdaSSA () (word (rhs.denote env)) () := by
  cases rhs with
  | constant => exact .op .unit rfl
  | binary op x y =>
      exact .op (.pair (.var_of_eq (env_lookup x env tail)) (.var_of_eq (env_lookup y env tail)))
        (by simp [instr, Prim.run, readWord, word, Rhs.denote])

private theorem term_eval (block : MLIR.Arith.Block Γ w) (env : Env Γ) (tail : Semantics.Env Atom) :
    Semantics.Tm.Eval instr (env.toLambdaSSA tail) block.toTerm () (word (block.denote env)) () := by
  induction block generalizing tail with
  | yield x => exact .var_of_eq (env_lookup x env tail)
  | letOp rhs _ ih =>
      exact .let₁ (rhs_eval rhs env tail) (ih (.cons (rhs.denote env) env) tail)
  | letRegion arg body _ bodyIH restIH =>
      let localEnv := Env.cons (env.get arg) .nil
      exact .let₁
        (.let₁ (.var_of_eq (env_lookup arg env tail)) (bodyIH localEnv (env.toLambdaSSA tail)))
        (restIH (.cons (body.denote localEnv) env) tail)

private theorem instr_deterministic : Semantics.InstrDeterministic instr := by
  intro _ _ _ _ _ _ _ left right
  exact ⟨Option.some.inj (left.symm.trans right), Subsingleton.elim _ _⟩

theorem toLambdaSSA_eval_iff (block : MLIR.Arith.Block Γ w) (env : Env Γ) (label : Nat) (out : Value Atom) :
    Semantics.Region.Eval instr env.toLambdaSSA block.toLambdaSSA () label out () ↔
      label = 0 ∧ out = word (block.denote env) := by
  have expected := Semantics.Region.Eval.br (label := 0) (term_eval block env (fun _ => .unit))
  constructor
  · intro run
    obtain ⟨sameLabel, sameOut, _⟩ := run.deterministic instr_deterministic expected
    exact ⟨sameLabel, sameOut⟩
  · rintro ⟨rfl, rfl⟩
    exact expected

end Silmaril.Proofs.MLIR.Arith
