module

public import Silmaril.SSA.MLIR.Arith.Thms
public import Silmaril.SSA.Isotope.Institution.Thms

/-! The existing single-exit LambdaSSA encoding applied to arithmetic blocks. -/

@[expose] public section

namespace Silmaril.MLIR.Arith

open Silmaril.Isotope
open Silmaril.Isotope.Morphism

/-- The lowered LambdaSSA region, with its single exit and input scope witnessed
by the typing derivation. -/
def Block.toScopedLambdaSSA {Γ : List Width} {w : Width} (block : Block Γ w) :
    SSAIter.ScopedRegion Prim 1 Γ.length :=
  ⟨block.toLambdaSSA, by simpa using block.toLambdaSSA_hasType.scoped⟩

/-- Encode the same scoped LambdaSSA region as a positional LetIter term. -/
def Block.toLetIter {Γ : List Width} {w : Width} (block : Block Γ w) :
    LetIter.LocallyNameless.Tm Empty Prim Γ.length :=
  SSAIter.encodeSingle block.toScopedLambdaSSA.val block.toScopedLambdaSSA.property

/-- Read the LambdaSSA environment at LetIter's in-scope indices. -/
def Env.toLetIter {Γ : List Width} (env : Env Γ) : LetIter.Semantics.BoundEnv Atom Γ.length :=
  fun i => env.toLambdaSSA (tail := fun _ => .unit) i.val

/-- The same value context in LetIter's length-indexed presentation. -/
def letIterContext : (Γ : List Width) → BoundCtx (Ty Width) Γ.length
  | [] => .nil
  | w :: Γ => .snoc (letIterContext Γ) (.base w)

end Silmaril.MLIR.Arith
