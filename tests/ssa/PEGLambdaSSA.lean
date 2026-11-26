module

import Silmaril.SSA.PEG.Bridge.LambdaSSA.Thms
import Silmaril.SSA.PEG.Builder

namespace Silmaril.SSA.PEG.Bridge.LambdaSSA.Tests

open RVSDG (Port Tuple)
open Simple (Code)
open Silmaril.SSA.SeaOfNodes
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

private abbrev num : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | high : Instr [num] .bool
  | addCount : Instr [num, .count] num
  | subCount : Instr [num, .count] num
  | sum : Instr [num, num] num

private def model : TotalModel Instr where
  carrier _ := Nat
  run
    | .high, .cons v .nil => ⟨decide (5 ≤ (show Nat from v))⟩
    | .addCount, .cons v (.cons n .nil) => Nat.add v n.down
    | .subCount, .cons v (.cons n .nil) => Nat.sub v n.down
    | .sum, .cons x (.cons y .nil) => Nat.add x y

private abbrev params : List (Ty Unit) := [num, .count]
private abbrev shared : List (Ty Unit) := [.bool, .count, num]
private abbrev results : List (Ty Unit) := [num, .count, num, num]

private def sharedCode : Code Instr params [] shared :=
  .emit (.emit (.emit .empty (.param .head) .nil) (.param (.tail .head)) .nil)
    (.op .high) (.cons (.tail .head) .nil)

private def onTrue : Arm Instr params shared results where
  nodes := num :: num :: shared
  code :=
    .emit (.emit .empty (.op .addCount) (.cons (.tail (.tail .head)) (.cons (.tail .head) .nil)))
      (.op .sum) (.cons .head (.cons .head .nil))
  outputs := .cons (.tail .head)
    (.cons (.tail (.tail (.tail .head))) (.cons .head (.cons (.tail .head) .nil)))

private def onFalse : Arm Instr params shared results where
  nodes := num :: shared
  code :=
    .emit .empty (.op .subCount) (.cons (.tail (.tail .head)) (.cons (.tail .head) .nil))
  outputs := .cons (.tail (.tail (.tail .head)))
    (.cons (.tail (.tail .head)) (.cons .head (.cons (.tail (.tail (.tail .head))) .nil)))

private def diamond : ScopedDiamond Instr params results where
  shared := shared
  sharedCode := sharedCode
  guard := .head
  onTrue := onTrue
  onFalse := onFalse

-- The true-arm slot belongs to its extended context. The false arm starts at
-- the shared context, where a reference with that context is ill-typed.
example (_trueLocal : Port onTrue.nodes num) : True := by
  fail_if_success
    have forbidden : Port shared num := _trueLocal
  trivial

private def input (v : Nat) : Tuple model.toPEG.Value params := .cons v (.cons ⟨2⟩ .nil)

private def expected (x y : Nat) : Tuple model.toPEG.Value results :=
  .cons x (.cons ⟨2⟩ (.cons y (.cons x .nil)))

private def packet (xs : Tuple model.toPEG.Value results) :
    Value (Diamond.LambdaSSA.Atom (Target.model model)) :=
  Diamond.LambdaSSA.encodeTuple (Target.model model) (Target.pack (F := Target.ValueAt model) xs)

private noncomputable def observe (v : Nat) : Tuple (fun t => Option (model.toPEG.Value t)) results :=
  diamond.toPEG.observe model.toPEG
    (diamond.toPEG.denote model.toPEG (input v) diamond.peg_wellFounded) Fin.elim0

private theorem observe_true : observe 7 = (expected 9 18).map (fun _ => some) := by
  refine (diamond.observe_diamond model (input 7) diamond.peg_wellFounded Fin.elim0).trans ?_
  rfl

private theorem observe_false : observe 3 = (expected 3 1).map (fun _ => some) := by
  refine (diamond.observe_diamond model (input 3) diamond.peg_wellFounded Fin.elim0).trans ?_
  rfl

example : diamond.lower.HasType (Diamond.LambdaSSA.initialContext (Target.sorts params))
    [Diamond.Arms.LambdaSSA.resultCode (Target.sorts results)] :=
  diamond.lower_hasType

private abbrev run (v label : Nat) (payload : Value (Diamond.LambdaSSA.Atom (Target.model model)))
    (initial final : Nat) :=
  Semantics.Region.Eval (Diamond.LambdaSSA.instruction (Target.model model))
    (Diamond.LambdaSSA.inputEnv (Target.model model) (Target.entry model (input v)))
    diamond.lower initial label payload final

-- Both control edges transfer a mixed-sort, ordered packet to the same join.
example : run 7 0 (packet (expected 9 18)) 42 42 :=
  (diamond.lower_eval_iff model (input 7) diamond.peg_wellFounded Fin.elim0 42 42 0 _).mpr
    ⟨rfl, rfl, expected 9 18, observe_true, rfl⟩

example : run 3 0 (packet (expected 3 1)) 42 42 :=
  (diamond.lower_eval_iff model (input 3) diamond.peg_wellFounded Fin.elim0 42 42 0 _).mpr
    ⟨rfl, rfl, expected 3 1, observe_false, rfl⟩

example : ¬ run 7 2 (packet (expected 9 18)) 42 42 :=
  fun h =>
    (by decide : (2 : Nat) ≠ 0)
      ((diamond.lower_eval_iff model (input 7) diamond.peg_wellFounded Fin.elim0 42 42 2 _).mp h).1

example : ¬ run 3 0 (packet (expected 3 1)) 42 43 :=
  fun h =>
    (by decide : (43 : Nat) ≠ 42)
      ((diamond.lower_eval_iff model (input 3) diamond.peg_wellFounded Fin.elim0 42 43 0 _).mp h).2.1

-- The doubled operand reads the same PEG vertex at both argument positions.
example : refNumbers (diamond.toPEG.node ⟨5, by decide⟩).args = [6, 6] := rfl

-- The two occurrence-indexed edges enter the join at label two. The Region's
-- first predecessor is the false projection.
example : (Target.graph diamond).merge.predecessor .first = .onFalse := rfl
example : Diamond.Arms.LambdaSSA.incoming (Target.graph diamond) .onTrue ≠
    Diamond.Arms.LambdaSSA.incoming (Target.graph diamond) .onFalse :=
  Diamond.Arms.LambdaSSA.incoming_distinct (Target.graph diamond)
example :
    (Diamond.Arms.LambdaSSA.phiView (Target.graph diamond)).table.branch
      (Diamond.Arms.LambdaSSA.edge (Target.graph diamond) .first) =
    .br 2 (PhiView.packTerm (Diamond.Arms.LambdaSSA.armArgs (Target.graph diamond) .onFalse)) :=
  Diamond.Arms.LambdaSSA.edge_branch (Target.graph diamond) .first

end Silmaril.SSA.PEG.Bridge.LambdaSSA.Tests
