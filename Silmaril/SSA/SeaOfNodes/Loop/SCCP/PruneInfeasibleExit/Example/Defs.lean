module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Bank.Defs

/-! A mixed-width bank with feedback that reads two different old fields. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example

open PruneExit (InputFacts)
open PruneExit.Example.Bank (i8 i16)
open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF (evalOp)
open Loop.MLIR.CF.Bank (Label)
open Silmaril.MLIR.Arith (Env Width)
open Semantics.Dataflow (Flat)

abbrev Carried := [i8, i16, i8]

abbrev EntrySigs : List (List (Diamond.Ty Width)) :=
  [[.value (.data i8)], [.value (.data i16)], [.value (.data i8)]]

abbrev HeaderSigs : List (List (Diamond.Ty Width)) :=
  [[.value (.data i8)], [.value (.data i16)], [.value .predicate],
    [.value (.data i8)], [.value (.data i16)]]

/-- Start at (1, 300, 4). With flag zero, update (a, payload, b) to
(b, payload + 2, a + 1), reading all three from the old bank. -/
def graph : Loop.MLIR.CF.Bank.Program [i8] Carried i16 EntrySigs HeaderSigs where
  preheader :=
    .cons (.arithmetic (.constant (1 : Word i8))) .nil
      (.cons (.arithmetic (.constant (300 : Word i16))) .nil
        (.cons (.arithmetic (.constant (4 : Word i8))) .nil .nil))
  header :=
    .cons (.arithmetic (.constant (1 : Word i8))) .nil
      (.cons (.arithmetic (.constant (2 : Word i16))) .nil
        (.cons (.ult i8) (.cons (.arg .head) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons (.arithmetic (.binary .addi))
            (.cons (.arg (.tail .head)) (.cons (.output (0 : Fin 3) .head) .nil))
            (.cons (.arithmetic (.binary .addi))
              (.cons (.arg (.tail (.tail .head))) (.cons (.output (1 : Fin 4) .head) .nil)) .nil))))
  phiInputs
    | .entry => .cons (.output (0 : Fin 3) .head)
        (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil))
    | .backedge => .cons (.arg (.tail (.tail (.tail .head))))
        (.cons (.output (4 : Fin 5) .head) (.cons (.output (3 : Fin 5) .head) .nil))
  predicate := .output (2 : Fin 5) .head
  result := .arg (.tail (.tail .head))

def facts (flag : Flat (Word i8)) : InputFacts [i8] := .cons flag .nil

def input (flag : Word i8) : Env [i8] := .cons flag .nil

/-- Inspect one actual pruned header step, including every routed operand. -/
def route (a : Word i8) (payload : Word i16) (b : Word i8) : Option (Nat × Nat × Nat) :=
  (rewrite graph (facts (.constant 0))).bind fun cfg =>
    match (cfg.block .header).eval evalOp (fun term env => term.eval env)
        (.cons a (.cons payload (.cons b (input 0)))) with
    | .inl frame => read frame.label frame.args
    | .inr _ => none
where
  read {args : List Width} : Label Carried i16 args → Env args → Option (Nat × Nat × Nat)
    | .header, .cons a (.cons payload (.cons b .nil)) => some (a.toNat, payload.toNat, b.toNat)
    | .exit, _ => none

/-- Outer `none` is rewrite refusal. `some none` is exhaustion of the target budget. -/
def run (flagFact : Flat (Word i8)) (fuel : Nat) (flag : Word i8) : Option (Option Nat) :=
  (rewrite graph (facts flagFact)).map fun cfg =>
    (cfg.run evalOp fuel (input flag)).map fun result => (result.get .here).toNat

/-- A genuinely varying guard on the earlier mixed-width counter is refused. -/
def refusesVarying : Bool :=
  (rewrite PruneExit.Example.Bank.graph PruneExit.Example.Bank.varyingFacts).isNone

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example
