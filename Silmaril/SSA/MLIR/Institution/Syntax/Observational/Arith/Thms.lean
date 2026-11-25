module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Arith.Defs
public import Silmaril.SSA.MLIR.Institution.Arith.Thms
public import Silmaril.SSA.MLIR.Arith.Examples.Thms
import Silmaril.Proofs.SSA.MLIR.Institution.Syntax.Observational.Arith.Comparison

public section

namespace Silmaril.MLIR.Institution.Syntax.Observational.Arith

open Silmaril.MLIR.Arith (Width Env Atom instr)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.Morphism
open Silmaril.MLIR.Arith.Examples (doubleAdd doubleMul i8)

variable {Γ : List Width} {w : Width}

/-- Equality in the arithmetic quotient means equality on all typed environments. -/
theorem arrow_eq_iff (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ env : Env Γ, b.denote env = c.denote env :=
  Proofs.MLIR.Institution.Syntax.Observational.Arith.arrow_eq_iff b c

/-- Compare return observations at the concrete arithmetic instructions and typed inputs. -/
theorem arrow_eq_iff_lambdaSSA_eval (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ (env : Env Γ) (label : Nat) (out : Value Atom),
      Semantics.Region.Eval instr env.toLambdaSSA b.toLambdaSSA () label out () ↔
        Semantics.Region.Eval instr env.toLambdaSSA c.toLambdaSSA () label out () :=
  Proofs.MLIR.Institution.Syntax.Observational.Arith.arrow_eq_iff_lambdaSSA_eval b c

/-- The same common slice has the same return observations through the LetIter encoding. -/
theorem arrow_eq_iff_letIter_eval (b c : Silmaril.MLIR.Arith.Block Γ w) :
    arrow b = arrow c ↔ ∀ (env : Env Γ) (out : Value Atom),
      LetIter.Semantics.Eval instr Empty.elim env.toLetIter b.toLetIter () out () ↔
        LetIter.Semantics.Eval instr Empty.elim env.toLetIter c.toLetIter () out () :=
  Proofs.MLIR.Institution.Syntax.Observational.Arith.arrow_eq_iff_letIter_eval b c

/-- Universal LambdaSSA observations imply equality on the concrete common slice. -/
theorem arrow_eq_of_lambdaSSA_obs (b c : Silmaril.MLIR.Arith.Block Γ w)
    (h : Region.Obs.{0, 0, 0} b.toLambdaSSA c.toLambdaSSA) : arrow b = arrow c :=
  (arrow_eq_iff_lambdaSSA_eval b c).mpr (fun _ _ _ => h.eval)

/-- Universal LetIter observations imply equality on the concrete common slice. -/
theorem arrow_eq_of_letIter_obs (b c : Silmaril.MLIR.Arith.Block Γ w)
    (h : LetIter.LocallyNameless.Tm.Obs.{0, 0, 0, 0} b.toLetIter c.toLetIter) :
    arrow b = arrow c :=
  (arrow_eq_iff_letIter_eval b c).mpr (fun _ _ => h.eval)

theorem double_eq (w : Width) : arrow (doubleAdd w) = arrow (doubleMul w) :=
  (arrow_eq_iff _ _).mpr (Silmaril.MLIR.Arith.Examples.double_lowering w)

/-- An alternative instruction relation distinguishes the two LambdaSSA lowerings. -/
theorem double_not_lambdaSSA_obs :
    ¬ Region.Obs.{0, 0, 0} (doubleAdd i8).toLambdaSSA (doubleMul i8).toLambdaSSA :=
  Proofs.MLIR.Institution.Syntax.Observational.Arith.double_not_lambdaSSA_obs

/-- The single-exit encoding preserves the distinction in the universal LetIter observations. -/
theorem double_not_letIter_obs :
    ¬ LetIter.LocallyNameless.Tm.Obs.{0, 0, 0, 0} (doubleAdd i8).toLetIter (doubleMul i8).toLetIter :=
  fun h => double_not_lambdaSSA_obs ((SSAIter.encodeSingle_obs_iff _ _).mp h)

end Silmaril.MLIR.Institution.Syntax.Observational.Arith
