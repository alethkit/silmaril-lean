module

import Silmaril.SSA.RVSDG.MLIR.Regionless.Thms

namespace Silmaril.SSA.RVSDG.MLIR.Regionless.Tests

open Silmaril.MLIR.Institution (OpArity Profile)

set_option backward.isDefEq.respectTransparency false

private inductive ValueSort where
  | nat
  | flag

private abbrev args : List ValueSort := [.nat, .flag]
private abbrev pair : List ValueSort := [.flag, .nat]
private abbrev outs : List ValueSort := [.nat, .flag, .nat]

private inductive Symbols : {a : OpArity false} → Profile a ValueSort → Type where
  | split : Symbols (profile id args pair)
  | finish : Symbols (profile id pair [.nat])

private abbrev target : Silmaril.MLIR.Institution.Signature false := ⟨ValueSort, Symbols⟩

private abbrev ports := valuePorts (V := ValueSort) Unit

private inductive Ops : Dialect ValueSort Unit where
  | split : Ops (ports args) (ports pair)
  | finish : Ops (ports pair) (ports [.nat])

private def matching : ProfileMap Ops target where
  sort := id
  symbol
    | .split => .symbol Symbols.split
    | .finish => .symbol Symbols.finish

private def carrier : ValueSort → Type
  | .nat => Nat
  | .flag => Bool

private def finishValue (flag : Bool) (n : Nat) : Nat :=
  if flag then n * 2 else n

private def model : Silmaril.MLIR.Institution.Model target where
  carrier := carrier
  op
    | .split, env, _ => Fin.cases (motive := fun i => carrier (context id pair i))
        (!(env 1)) (Fin.cases (Nat.succ (env 0)) (fun i => i.elim0))
    | .finish, env, _ => Fin.cases (motive := fun i => carrier (context id [.nat] i))
        (finishValue (env 0) (env 1)) (fun i => i.elim0)

private def splitNode : Node Ops (ports args) [] (ports pair) :=
  ⟨ports args, .simple .split, .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), Fin.elim0⟩

private def finishNode : Node Ops (ports args) [ports pair] (ports [.nat]) :=
  ⟨ports pair, .simple .finish, .cons (.output 0 .head) (.cons (.output 0 (.tail .head)) .nil),
    Fin.elim0⟩

-- The two result slots of split feed a second binding. The graph then returns
-- its results out of vertex order and uses the second node's value twice.
private abbrev vertices : List (Ports (PortType ValueSort Unit)) := [ports pair, ports [.nat]]

private def term : Term Ops (ports args) [] vertices (ports outs) :=
  .bind splitNode (fun i => i.elim0) (.bind finishNode (fun i => i.elim0)
    (.ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)))))

private def graph := term.toGraph

private def env : Silmaril.MLIR.Institution.Assignment model.carrier (context matching.sort args) :=
  Fin.cases (motive := fun i => carrier (context id args i)) (10 : Nat) (Fin.cases false (fun i => i.elim0))

example : (translateGraph matching graph 0).denote model env = (22 : Nat) := rfl
example : (translateGraph matching graph 1).denote model env = true := rfl
example : (translateGraph matching graph 2).denote model env = (22 : Nat) := rfl

private def passthrough : Term Ops (ports args) [] [] (ports outs) :=
  .ret (.cons (.arg .head) (.cons (.arg (.tail .head)) (.cons (.arg .head) .nil)))

private def equation : ValueEquation Ops := ⟨args, outs, vertices, [], graph, passthrough.toGraph⟩

example : ¬ equation.toRVSDG.Holds (matching.pullback model) := by
  intro holds
  have output := (satisfaction matching model equation).mpr holds env (1 : Fin 3)
  change true = false at output
  cases output

-- A nonidentity opcode map identifies two otherwise identical
-- instructions. The square holds at the syntax level, including shared results.
private inductive Aliases : Dialect ValueSort Unit where
  | first : Aliases (ports args) (ports pair)
  | second : Aliases (ports args) (ports pair)
  | finish : Aliases (ports pair) (ports [.nat])

private def toOps : Institution.OpcodeMap Aliases Ops
  | _, _, .first | _, _, .second => .split
  | _, _, .finish => .finish

private def aliased : ValueEquation Aliases :=
  let rename : Institution.OpcodeMap Ops Aliases := fun op => match op with
    | .split => .second
    | .finish => .finish
  equation.map rename

example : translateEquation (matching.precomp toOps) aliased =
    translateEquation matching (aliased.map toOps) :=
  translateEquation_precomp matching toOps aliased

end Silmaril.SSA.RVSDG.MLIR.Regionless.Tests
