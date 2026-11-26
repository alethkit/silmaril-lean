module

import Silmaril.SSA.PEG.Bridge.MLIR.Thms
import Silmaril.SSA.PEG.Bridge.LambdaSSA.Thms
import Silmaril.SSA.PEG.Builder

namespace Silmaril.SSA.PEG.Bridge.Tests

open RVSDG (Tuple)
open Silmaril.SSA.RVSDG.MLIR

private abbrev num : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | ten : Instr [] num
  | mix : Instr [num, .count, num] num
  | sub : Instr [num, num] num

private def model : TotalModel Instr where
  carrier _ := Nat
  run
    | .ten, .nil => (10 : Nat)
    | .mix, .cons x (.cons k (.cons y .nil)) => Nat.add (Nat.mul x k.down) y + 6
    | .sub, .cons x (.cons y .nil) => Nat.sub x y

private abbrev params : List (Ty Unit) := [.bool, num, .count]
private abbrev results : List (Ty Unit) := [num, num, num, .count, num]
private def sorts (i : Fin 7) : Ty Unit :=
  if i.val = 0 then .bool else if i.val = 2 then .count else num

private def graph : Graph Instr params results 7 0 where
  forest := ⟨Fin.elim0⟩
  sort := sorts
  node
    | ⟨0, _⟩ => .ofLabel (.param .head) .nil
    | ⟨1, _⟩ => .ofLabel (.param (.tail .head)) .nil
    | ⟨2, _⟩ => .ofLabel (.param (.tail (.tail .head))) .nil
    | ⟨3, _⟩ => .ofLabel (.op .ten) .nil
    | ⟨4, _⟩ => .ofLabel (.op .mix) (.cons ⟨1, rfl⟩ (.cons ⟨2, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨5, _⟩ => .ofLabel (.op .sub) (.cons ⟨4, rfl⟩ (.cons ⟨3, rfl⟩ .nil))
    | ⟨6, _⟩ => .ofLabel .phi (.cons ⟨0, rfl⟩ (.cons ⟨5, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))
    | ⟨i + 7, h⟩ => False.elim (by omega)
  roots := .cons ⟨6, rfl⟩ (.cons ⟨4, rfl⟩ (.cons ⟨6, rfl⟩
    (.cons ⟨2, rfl⟩ (.cons ⟨5, rfl⟩ .nil))))

private theorem ordered : Ordered graph := by decide

private def input (flag : Bool) : Tuple model.toPEG.Value params :=
  .cons ⟨flag⟩ (.cons (4 : Nat) (.cons ⟨2⟩ .nil))

private def expected (answer : Nat) : Tuple model.toPEG.Value results :=
  .cons answer (.cons (18 : Nat) (.cons answer (.cons ⟨2⟩ (.cons (8 : Nat) .nil))))

private def runRVSDG (flag : Bool) : Tuple model.toPEG.Value results :=
  fromPorts results ((translate graph ordered).2.run model.toRVSDG (toPorts (input flag)))

private def runMLIR (flag : Bool) : Tuple model.toPEG.Value results :=
  fromPorts results (Regionless.ofAssignment (F := model.toRVSDG.Val) results (fun i =>
    (translateMLIR graph ordered i).denote model.toMLIR
      (Regionless.toAssignment params (toPorts (F := model.toRVSDG.Val) (input flag)))))

example : runRVSDG true = expected 8 := rfl
example : runRVSDG false = expected 4 := rfl
example : runMLIR true = expected 8 := rfl
example : runMLIR false = expected 4 := rfl

private def producers {past : List (List (ValuePort Unit))} :
    {ts : List (ValuePort Unit)} → RVSDG.Wires (valuePorts params) past ts → List (Option Nat)
  | _, .nil => []
  | _, .cons wire rest => wire.producer :: producers rest

-- Both repeated operands keep the same numbered producer in the target graph.
example : producers ((translate graph ordered).2.nodes ⟨4, by decide⟩).inputs =
    [some 1, some 2, some 1] := rfl

private noncomputable def runPEG (flag : Bool) :
    Tuple (fun t => Option (model.toPEG.Value t)) results :=
  graph.observe model.toPEG (graph.denote model.toPEG (input flag) ordered.demandWellFounded) Fin.elim0

example : runPEG true = (expected 8).map (fun _ => some) := by
  rw [runPEG, observe_translate graph ordered]
  rfl

example : runPEG false = (expected 4).map (fun _ => some) := by
  rw [runPEG, observe_translateMLIR graph ordered]
  rfl

-- Changing a primitive to read its own output keeps the wiring typed.
private def selfEdge : Graph Instr [] [num] 1 0 where
  forest := ⟨Fin.elim0⟩
  sort _ := num
  node _ := .ofLabel (.op .sub) (.cons ⟨0, rfl⟩ (.cons ⟨0, rfl⟩ .nil))
  roots := .cons ⟨0, rfl⟩ .nil

example : ¬ Ordered selfEdge := by decide

-- The actual primitive equation is strict, even when its primitive ignores all arguments.
private def ignoresArgs : Interpretation Instr :=
  ⟨model.carrier, fun
    | .ten, _ => some (1 : Nat)
    | .mix, _ => some (1 : Nat)
    | .sub, _ => some (1 : Nat)⟩

private def missingRhs (s : Fin [num, num].length) : Option (ignoresArgs.Value [num, num][s]) :=
  Fin.cases (motive := fun i => Option (ignoresArgs.Value [num, num][i])) (some (7 : Nat)) (fun _ => none) s

example : (Label.op Instr.sub : Label Instr [] (Fin 0) [num, num] num).interpret
    ignoresArgs .nil Fin.elim0 (fun s _ _ => missingRhs s) = none :=
  interpret_op_eq_none ignoresArgs .nil Fin.elim0 .sub _ 1 rfl

-- The Figure 11 conditional still reads only the selected arm.
private def unselectedBottom (s : Fin [Ty.bool, num, num].length) :
    Option (model.toPEG.Value [Ty.bool, num, num][s]) :=
  Fin.cases (motive := fun i => Option (model.toPEG.Value [Ty.bool, num, num][i]))
    (some ⟨true⟩) (Fin.cases (some (7 : Nat)) (fun _ => none)) s

example : (Label.phi : Label Instr [] (Fin 0) [.bool, num, num] num).interpret
    model.toPEG .nil Fin.elim0 (fun s _ _ => unselectedBottom s) = some (7 : Nat) := rfl

end Silmaril.SSA.PEG.Bridge.Tests

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
