module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs

/-! A counter with differently typed carried words and distinct exit and feedback operands. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Bank

open SeaOfNodes.MLIR (Word)
open Loop.MLIR.CF (evalOp)
open Silmaril.MLIR.Arith (Env Width)

def i8 : Width := ⟨8, by decide⟩
def i16 : Width := ⟨16, by decide⟩

abbrev Inputs := [i8, i16, i8]
abbrev Carried := [i8, i16]

abbrev HeaderSigs : List (List (Diamond.Ty Width)) :=
  [[.value (.data i8)], [.value (.data i16)], [.value .predicate],
    [.value (.data i8)], [.value (.data i16)]]

/-- Test the first latch against the captured limit. On feedback increment
the first latch by one and the second by two. On exit return the old second latch. -/
def graph : Loop.MLIR.CF.Bank.Program Inputs Carried i16 [] HeaderSigs where
  preheader := .nil
  header :=
    let counter := RVSDG.Port.tail (.tail (.tail .head))
    let payload := RVSDG.Port.tail (.tail (.tail (.tail .head)))
    let limit := RVSDG.Port.tail (.tail .head)
    .cons (.arithmetic (.constant (1 : Word i8))) .nil
      (.cons (.arithmetic (.constant (2 : Word i16))) .nil
        (.cons (.ult i8) (.cons (.arg counter) (.cons (.arg limit) .nil))
          (.cons (.arithmetic (.binary .addi))
            (.cons (.arg counter) (.cons (.output (0 : Fin 3) .head) .nil))
            (.cons (.arithmetic (.binary .addi))
              (.cons (.arg payload) (.cons (.output (1 : Fin 4) .head) .nil)) .nil))))
  phiInputs
    | .entry => .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)
    | .backedge => .cons (.output (3 : Fin 5) .head) (.cons (.output (4 : Fin 5) .head) .nil)
  predicate := .output (2 : Fin 5) .head
  result := .arg (.tail (.tail (.tail (.tail .head))))

def input (start : Word i8) (payload : Word i16) (limit : Word i8) : Env Inputs :=
  .cons start (.cons payload (.cons limit .nil))

def exitFacts : InputFacts Inputs :=
  .cons (.constant (5 : Word i8)) (.cons .overdefined (.cons (.constant (4 : Word i8)) .nil))

def varyingFacts : InputFacts Inputs :=
  .cons (.constant (2 : Word i8)) (.cons .overdefined (.cons (.constant (4 : Word i8)) .nil))

def unknownFacts : InputFacts Inputs :=
  .cons .overdefined (.cons .overdefined (.cons (.constant (4 : Word i8)) .nil))

def unseenFacts : InputFacts Inputs :=
  .cons .bottom (.cons .overdefined (.cons (.constant (4 : Word i8)) .nil))

/-- Outer `none` is refusal. `some none` is target budget exhaustion. -/
def run (facts : InputFacts Inputs) (budget : Nat) (start : Word i8) (payload : Word i16) : Option (Option Nat) :=
  (PruneExit.Bank.rewrite graph facts).map fun cfg =>
    (cfg.run evalOp budget (input start payload 4)).map fun result => (result.get .here).toNat

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Bank
