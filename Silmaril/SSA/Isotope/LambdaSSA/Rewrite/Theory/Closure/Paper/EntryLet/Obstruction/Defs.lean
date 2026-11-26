module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Resumption.Thms

/-! # A terminating observation for flat CFG sequencing -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction

open SequencingObstruction (Instruction)

abbrev U : Ty Empty := .unit

/-- A terminating run records its exact exit, payload, and diagnostic bits. -/
structure Observation where
  label : Nat
  payload : Value Empty
  effect : Bool
  marked : Bool

/-- Acyclic forwarding from local label zero through label one to the outward exit. -/
def blocks : Fin 2 → Region Instruction :=
  Fin.cases (.br 1 (.var 0)) (fun _ => .br 2 (.var 0))

def request : Tm Instruction := .op .tick (.var 0)

def flatRequest : Region Instruction := .cfg (.let₁ request (.br 0 (.var 0))) 2 blocks

def movedRequest : Region Instruction :=
  .let₁ request (.cfg (.br 0 (.var 0)) 2
    (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift Nat.succ)))

def unaryBlock : Region Instruction := .br 1 (.var 0)

/-- Run the request under a unary binder before the two local transfers. -/
def nestedRequest : Region Instruction :=
  .cfg (CfgEta.singleCfg (.let₁ request (.br 0 (.var 0))) unaryBlock) 2 blocks

/-- Move the let within the outer scope using the unary sequencing equation. -/
def nestedMoved : Region Instruction :=
  .cfg (.let₁ request (CfgEta.singleCfg (.br 0 (.var 0))
    (unaryBlock.renameVars (Silmaril.DeBruijn.lift Nat.succ)))) 2 blocks

def unitEnv : Semantics.Env Empty := fun _ => .unit

def finish (mark : Bool) : Observation := ⟨0, .unit, true, mark⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.EntryLetObstruction
