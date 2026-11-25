module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Arith.Defs
public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Thms
public import Silmaril.SSA.MLIR.Institution.Arith.Thms
public import Silmaril.SSA.MLIR.Arith.Examples.Thms

public section

namespace Silmaril.Proofs.MLIR.Institution.Syntax.Observational.Arith

open Silmaril.MLIR.Institution (Assignment)
open Silmaril.MLIR.Institution.Arith (model assignment translate_denote)
open Silmaril.MLIR.Institution.Syntax.Observational (ofBlock_eq_iff)
open Silmaril.MLIR.Institution.Syntax.Observational.Arith
open Silmaril.MLIR.Arith (Width Env Atom Prim instr word)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA

variable {Γ : List Width} {w : Width}

private theorem assignment_surjective (Γ : List Width) :
    Function.Surjective (assignment (Γ := Γ)) := by
  induction Γ with
  | nil => exact fun _ => ⟨.nil, funext fun i => Fin.elim0 i⟩
  | cons w Γ ih =>
    intro e
    obtain ⟨tail, ht⟩ := ih (fun j => e j.succ)
    exact ⟨.cons (e 0) tail, funext (Fin.cases rfl fun j => congrFun ht j)⟩

theorem arrow_eq_iff (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ env : Env Γ, b.denote env = c.denote env := by
  refine ofBlock_eq_iff.trans ⟨?_, ?_⟩
  · intro h env
    exact (translate_denote b env).symm.trans
      ((h model rfl (assignment env) (0 : Fin 1)).trans (translate_denote c env))
  · intro h M hM e _
    subst M
    obtain ⟨env, rfl⟩ := assignment_surjective Γ e
    exact (translate_denote b env).trans ((h env).trans (translate_denote c env).symm)

private theorem word_injective : Function.Injective (word (w := w)) := by
  intro a b h
  cases h
  rfl

theorem arrow_eq_iff_lambdaSSA_eval (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ (env : Env Γ) (label : Nat) (out : Value Atom),
      Semantics.Region.Eval instr env.toLambdaSSA b.toLambdaSSA () label out () ↔
        Semantics.Region.Eval instr env.toLambdaSSA c.toLambdaSSA () label out () := by
  rw [arrow_eq_iff]
  constructor
  · intro h env label out
    simp only [b.toLambdaSSA_eval_iff, c.toLambdaSSA_eval_iff, h env]
  · intro h env
    have hb := (b.toLambdaSSA_eval_iff env 0 (word (b.denote env))).mpr ⟨rfl, rfl⟩
    exact word_injective ((c.toLambdaSSA_eval_iff env 0 _).mp ((h env 0 _).mp hb)).2

theorem arrow_eq_iff_letIter_eval (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ (env : Env Γ) (out : Value Atom),
      LetIter.Semantics.Eval instr Empty.elim env.toLetIter b.toLetIter () out () ↔
        LetIter.Semantics.Eval instr Empty.elim env.toLetIter c.toLetIter () out () := by
  rw [arrow_eq_iff]
  constructor
  · intro h env out
    simp only [b.toLetIter_eval_iff, c.toLetIter_eval_iff, h env]
  · intro h env
    have hb := (b.toLetIter_eval_iff env (word (b.denote env))).mpr rfl
    exact word_injective ((c.toLetIter_eval_iff env _).mp ((h env _).mp hb))

/-- An admissible observation model runs addition but supplies no step for constants. -/
private def addOnly : Prim → Value Atom → Unit → Value Atom → Unit → Prop
  | .binary .addi w, arg, s, out, t => instr (.binary .addi w) arg s out t
  | _, _, _, _, _ => False

open Silmaril.MLIR.Arith.Examples (doubleAdd doubleMul i8)

theorem double_not_lambdaSSA_obs :
    ¬ Region.Obs.{0, 0, 0} (doubleAdd i8).toLambdaSSA (doubleMul i8).toLambdaSSA := by
  intro h
  let env := (Env.cons (w := i8) 0#8 .nil).toLambdaSSA
  have add : Semantics.Region.Eval addOnly env (doubleAdd i8).toLambdaSSA () 0
      (word (w := i8) 0#8) () :=
    .br (.let₁ (.op (.pair .var .var) rfl) .var)
  have mul := h.eval.mp add
  cases mul with
  | br eval =>
    cases eval with
    | let₁ constant _ =>
      cases constant with
      | op _ step => exact step

end Silmaril.Proofs.MLIR.Institution.Syntax.Observational.Arith
