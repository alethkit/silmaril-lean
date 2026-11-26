module

import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.SSA.PEG.Simple.Structured.Thms
import Silmaril.SSA.PEG.Thms
import Silmaril.SSA.PEG.Simple.Structured.Completion.Thms
import Silmaril.SSA.PEG.Rules.Thms
meta import Silmaril.SSA.PEG.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Defs
meta import Silmaril.SSA.PEG.Simple.Structured.Completion.Defs
meta import Silmaril.SSA.PEG.Simple.While.Defs
meta import Silmaril.SSA.PEG.Simple.Defs

namespace Silmaril.SSA.PEG.Simple.Tests

open RVSDG (Port Tuple)

set_option backward.isDefEq.respectTransparency false

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | add : Op [.count, .count] .count
  | mul : Op [.count, .count] .count
  | pred : Op [.count] .count
  | positive : Op [.count] .bool
  | not : Op [.bool] .bool
  | bad : Op [] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .add, .cons a (.cons b .nil) => some ⟨a.down + b.down⟩
    | .mul, .cons a (.cons b .nil) => some ⟨a.down * b.down⟩
    | .pred, .cons a .nil => some ⟨a.down - 1⟩
    | .positive, .cons a .nil => some ⟨decide (0 < a.down)⟩
    | .not, .cons a .nil => some ⟨!a.down⟩
    | .bad, _ => none

private def entry (flag : Bool) (n : Nat) : Tuple model.Value [.bool, .count] :=
  .cons ⟨flag⟩ (.cons ⟨n⟩ .nil)

private def prependCount {ts : List (Ty Unit)} (n : Nat) (rest : Tuple model.Value ts) :
    Tuple model.Value (.count :: ts) :=
  .cons ⟨n⟩ rest

private def doubled {ctx : List (Ty Unit)} (slot : Port ctx .count) : Expr Op ctx .count :=
  .op .add (.cons (.var slot) (.cons (.var slot) .nil))

/-- A branch defines the same fresh slot on both paths. The next statement
uses that slot twice. The unchosen false arm has a partial primitive. -/
private def branchThenAssign : Program Op false [.bool, .count] .count where
  locals := [.count, .count, .bool, .count]
  body := .seq
    (.branch (.var .head) (.assign (doubled (.tail .head))) (.assign (.op .bad .nil)))
    (.assign (doubled .head))
  retvar := .head

private theorem branchReturns : branchThenAssign.Returns model (entry true 2) ⟨8⟩ := by
  refine ⟨.cons ⟨8⟩ (.cons ⟨4⟩ (entry true 2)), ?_, rfl⟩
  change Exec model (.seq (.branch (.var .head) (.assign (doubled (.tail .head)))
      (.assign (.op .bad .nil))) (.assign (doubled .head))) (entry true 2) _
  exact .seq (next := prependCount 4 (entry true 2))
    (.branchTrue rfl (.assign rfl)) (.assign rfl)

private noncomputable def observe {params : List (Ty Unit)} {t : Ty Unit}
    (p : Program Op false params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  p.translate.observe model
    (p.translate.denote model input (p.translate.demandWellFounded p.translate_wellFormed)) Index.zero

example : observe branchThenAssign (entry true 2) = .cons (some ⟨8⟩) .nil :=
  branchThenAssign.translate_returns model (entry true 2) branchReturns Index.zero

example : branchThenAssign.Fails model (entry false 2) := by
  change Exec model (.seq (.branch (.var .head) (.assign (doubled (.tail .head)))
      (.assign (.op .bad .nil))) (.assign (doubled .head))) (entry false 2) none
  exact .firstFailed (.branchFalse rfl (.assignFailed rfl))

-- Two parameters, the two arm expressions, three join results and the last instruction.
example : branchThenAssign.lower.nodes.length = 8 := by decide
example : refNumbers (branchThenAssign.translate.node ⟨0, by decide⟩).args = [1, 1] := by decide

private def chooseOld : Program Op false [.bool, .count] .count where
  locals := [.count]
  body := .branch (.var .head)
    (.seq (.assign (.op .bad .nil)) (.project (.cons .head .nil)))
    (.project (.cons (.tail .head) .nil))
  retvar := .head

example : observe chooseOld (entry false 31) = .cons (some ⟨31⟩) .nil := by
  refine chooseOld.translate_returns model (entry false 31) ?_ Index.zero
  exact ⟨.cons ⟨31⟩ .nil, .branchFalse rfl .project, rfl⟩

/-- The source still executes the discarded assignment. The PEG return
is allowed to depend only on the original parameter. -/
private def discardedFailure : Program Op false [.count] .count where
  locals := [.count]
  body := .seq (.assign (.op .bad .nil)) (.project (.cons (.tail .head) .nil))
  retvar := .head

private def seven : Tuple model.Value [.count] := .cons ⟨7⟩ .nil

example : discardedFailure.Fails model seven :=
  .firstFailed (.assignFailed rfl)

example : observe discardedFailure seven = .cons (some ⟨7⟩) .nil := by
  unfold observe Program.translate
  rw [Code.observe_toGraph]
  rfl

/-- The factorial body carries accumulator and counter. -/
private def factorialBody : Stmt Op false [.count, .count] [.count, .count] :=
  .seq (.assign (.op .mul (.cons (.var .head) (.cons (.var (.tail .head)) .nil))))
    (.seq (.assign (.op .pred (.cons (.var (.tail (.tail .head))) .nil)))
      (.project (.cons (.tail .head) (.cons .head .nil))))

private def factorialGuard : Expr Op [.count, .count] .bool :=
  .op .positive (.cons (.var (.tail .head)) .nil)

private def carry (acc n : Nat) : Tuple model.Value [.count, .count] :=
  .cons ⟨acc⟩ (.cons ⟨n⟩ .nil)

private def falling (acc : Nat) : Nat → Nat
  | 0 => acc
  | n + 1 => falling (acc * (n + 1)) n

private theorem factorialStep (acc n : Nat) :
    Exec model factorialBody.enableWhile (carry acc (n + 1)) (some (carry (acc * (n + 1)) n)) :=
  .seq (next := prependCount (acc * (n + 1)) (carry acc (n + 1))) (.assign rfl)
    (.seq (next := prependCount n (prependCount (acc * (n + 1)) (carry acc (n + 1))))
      (.assign rfl) .project)

private theorem factorialExec (acc n : Nat) :
    Exec model (.while rfl factorialGuard factorialBody.enableWhile) (carry acc n)
      (some (carry (falling acc n) 0)) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih => exact .whileStep rfl (factorialStep acc n) (ih (acc * (n + 1)))

private def factorial : WhileProgram Op [.count, .count] .count where
  guard := factorialGuard
  body := factorialBody
  retvar := .head

/-- Manually wired Trans-While instance. Both θ nodes share the iteration
coordinate, and both live variables use the same pass node. -/
private def factorialRaw : RawGraph Op [.count, .count] [.count, .count] 11 1 where
  forest := ⟨fun _ => none⟩
  sort i := if i = 6 ∨ i = 7 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .theta 0, [2, 4]⟩
    | 1 => ⟨_, .theta 0, [3, 5]⟩
    | 2 => ⟨_, .param .head, []⟩
    | 3 => ⟨_, .param (.tail .head), []⟩
    | 4 => ⟨_, .op .mul, [0, 1]⟩
    | 5 => ⟨_, .op .pred, [1]⟩
    | 6 => ⟨_, .op .positive, [1]⟩
    | 7 => ⟨_, .op .not, [6]⟩
    | 8 => ⟨_, .pass 0, [7]⟩
    | 9 => ⟨_, .eval 0, [0, 8]⟩
    | 10 => ⟨_, .eval 0, [1, 8]⟩
  roots := [9, 10]

private def factorialGraph : Graph Op [.count, .count] [.count, .count] 11 1 :=
  factorialRaw.check.get (by decide)

private def factorialRank : DemandRank 11 1 :=
  [.phase fun i => match i with
    | 6 => 1
    | 7 => 2
    | 8 => 3
    | 9 | 10 => 4
    | _ => 0,
   .counter 0,
   .phase fun i => match i with
    | 0 | 1 => 1
    | 4 | 5 => 2
    | _ => 0]

private noncomputable def factorialValue (acc n : Nat) : factorialGraph.Valuation model :=
  factorialGraph.denote model (carry acc n)
    (factorialGraph.demandWellFounded_of_check factorialRank (by decide))

private theorem factorialEq (acc n : Nat) (q : Request 11 1) :
    factorialValue acc n q = factorialGraph.equation model (carry acc n) (factorialValue acc n) q :=
  factorialGraph.denote_solves model (carry acc n) _ q

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem setClock (k j : Nat) : (clock k).set 0 j = clock j := by
  funext i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst i
  rfl

/-- The executable loop body can also be sampled beyond the first exit.
Only the prefix through that exit is used below. -/
private def accumulator (acc n : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => accumulator acc n k * (n - k)

private theorem collectSingle (t : Ty Unit) (read : (slot : Fin [t].length) →
    Option (model.Value [t][slot])) :
    collect [t] read = (read 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases read 0 <;> rfl

private theorem collectPair (read : (slot : Fin [Ty.count, Ty.count].length) →
    Option (model.Value [Ty.count, Ty.count][slot])) :
    collect [.count, .count] read =
      (read 0).bind (fun x => (read (0 : Fin 1).succ).map (fun y => .cons x (.cons y .nil))) := by
  unfold collect
  rw [collectSingle]
  cases read 0 <;> cases read (0 : Fin 1).succ <;> rfl

private theorem factorialSamples (acc n k : Nat) :
    factorialValue acc n (0, clock k) = some ⟨accumulator acc n k⟩ ∧
    factorialValue acc n (1, clock k) = some ⟨n - k⟩ := by
  induction k with
  | zero =>
    exact ⟨(factorialEq acc n (0, clock 0)).trans (factorialEq acc n (2, clock 0)),
      (factorialEq acc n (1, clock 0)).trans (factorialEq acc n (3, clock 0))⟩
  | succ k ih =>
    have a := factorialEq acc n (0, clock (k + 1))
    have b := factorialEq acc n (1, clock (k + 1))
    change factorialValue acc n (0, clock (k + 1)) =
      factorialValue acc n (4, (clock (k + 1)).set 0 k) at a
    change factorialValue acc n (1, clock (k + 1)) =
      factorialValue acc n (5, (clock (k + 1)).set 0 k) at b
    rw [setClock] at a b
    have mul := factorialEq acc n (4, clock k)
    have pred := factorialEq acc n (5, clock k)
    change _ = (collect (F := model.Value) [.count, .count] _).elim none (model.run .mul) at mul
    change _ = (collect (F := model.Value) [.count] _).elim none (model.run .pred) at pred
    rw [collectPair] at mul
    rw [collectSingle] at pred
    change _ = ((factorialValue acc n (0, clock k)).bind
      (fun x => (factorialValue acc n (1, clock k)).map (fun y => .cons x (.cons y .nil)))).elim
        none (model.run .mul) at mul
    change _ = ((factorialValue acc n (1, clock k)).map (fun x => .cons x .nil)).elim
      none (model.run .pred) at pred
    rw [ih.1, ih.2] at mul
    rw [ih.2] at pred
    have dec : n - k - 1 = n - (k + 1) := by omega
    exact ⟨a.trans mul, b.trans (pred.trans (congrArg (fun x => some (ULift.up x)) dec))⟩

private theorem factorialExit (acc n k : Nat) :
    factorialValue acc n (7, clock k) = some ⟨decide (n ≤ k)⟩ := by
  have positive := factorialEq acc n (6, clock k)
  have exit := factorialEq acc n (7, clock k)
  change _ = (collect (F := model.Value) [.count] _).elim none (model.run .positive) at positive
  change _ = (collect (F := model.Value) [.bool] _).elim none (model.run .not) at exit
  rw [collectSingle] at positive exit
  change _ = ((factorialValue acc n (1, clock k)).map (fun x => .cons x .nil)).elim
    none (model.run .positive) at positive
  change _ = ((factorialValue acc n (6, clock k)).map (fun x => .cons x .nil)).elim
    none (model.run .not) at exit
  rw [exit, positive, (factorialSamples acc n k).2]
  change some (ULift.up (!decide (0 < n - k))) = some (ULift.up (decide (n ≤ k)))
  by_cases h : n ≤ k
  · have zero : n - k = 0 := by omega
    simp [h, zero]
  · have pos : 0 < n - k := by omega
    simp [h, pos]

private theorem factorialPass (acc n : Nat) :
    factorialValue acc n (8, clock 0) = some ⟨n⟩ := by
  have e := factorialEq acc n (8, clock 0)
  change _ =
    (firstTrue (fun k => (factorialValue acc n (7, (clock 0).set 0 k)).map ULift.down)).map ULift.up at e
  have stream : (fun k => (factorialValue acc n (7, (clock 0).set 0 k)).map ULift.down) =
      fun k => some (decide (n ≤ k)) := by
    funext k
    rw [setClock, factorialExit]
    rfl
  have least : firstTrue (fun k => some (decide (n ≤ k))) = some n := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨by simp, fun _ _ => rfl⟩, ?_⟩
    intro j hj hit
    have defined := ((monotonize_eq_some_iff _ _ _).mp hit).1
    simp [Nat.not_le_of_lt hj] at defined
  rw [e, stream, least]
  rfl

private theorem factorialEval (acc n : Nat) :
    factorialGraph.observe model (factorialValue acc n) (clock 0) =
      .cons (some ⟨accumulator acc n n⟩) (.cons (some ⟨0⟩) .nil) := by
  have a := factorialEq acc n (9, clock 0)
  have b := factorialEq acc n (10, clock 0)
  change _ = (factorialValue acc n (8, clock 0)).elim none
    (fun k => monotonize (fun j => factorialValue acc n (0, (clock 0).set 0 j)) k.down) at a
  change _ = (factorialValue acc n (8, clock 0)).elim none
    (fun k => monotonize (fun j => factorialValue acc n (1, (clock 0).set 0 j)) k.down) at b
  rw [factorialPass] at a b
  change _ = monotonize (fun j => factorialValue acc n (0, (clock 0).set 0 j)) n at a
  change _ = monotonize (fun j => factorialValue acc n (1, (clock 0).set 0 j)) n at b
  have accAtExit := (monotonize_eq_some_iff (fun j => factorialValue acc n (0, (clock 0).set 0 j))
    n (ULift.up (accumulator acc n n))).mpr
    ⟨by rw [setClock, (factorialSamples acc n n).1], fun j _ => by
      rw [setClock, (factorialSamples acc n j).1]
      rfl⟩
  have countAtExit := (monotonize_eq_some_iff (fun j => factorialValue acc n (1, (clock 0).set 0 j))
    n (ULift.up 0)).mpr
    ⟨by rw [setClock, (factorialSamples acc n n).2, Nat.sub_self], fun j _ => by
      rw [setClock, (factorialSamples acc n j).2]
      rfl⟩
  change (Tuple.cons (F := fun t => Option (model.Value t)) (t := .count)
    (factorialValue acc n (9, clock 0))
    (.cons (t := .count) (factorialValue acc n (10, clock 0)) .nil)) = _
  rw [a, b, accAtExit, countAtExit]

private theorem accumulatorShift (acc n k : Nat) :
    accumulator acc (n + 1) (k + 1) = accumulator (acc * (n + 1)) n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change accumulator acc (n + 1) (k + 1) * ((n + 1) - (k + 1)) =
      accumulator (acc * (n + 1)) n k * (n - k)
    rw [ih, Nat.succ_sub_succ_eq_sub]

private theorem accumulatorExit (acc n : Nat) :
    accumulator acc n n = falling acc n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => exact (accumulatorShift acc n n).trans (ih (acc * (n + 1)))

/-- Every successful execution of the factorial source agrees with the
manually wired graph's accumulator result. -/
private theorem factorialPreserves (acc n : Nat) {value : model.Value .count}
    (run : factorial.source.Returns model (carry acc n) value) :
    factorialGraph.observe model (factorialValue acc n) (clock 0) =
      .cons (some value) (.cons (some ⟨0⟩) .nil) := by
  obtain ⟨final, exec, returned⟩ := run
  have same := Option.some.inj (exec.deterministic (factorialExec acc n))
  subst final
  rw [factorialEval, accumulatorExit, ← returned]
  rfl

example : factorialGraph.observe model (factorialValue 1 10) (clock 0) =
    .cons (some ⟨3628800⟩) (.cons (some ⟨0⟩) .nil) :=
  factorialPreserves 1 10 ⟨carry 3628800 0, factorialExec 1 10, rfl⟩

example : factorialGraph.observe model (factorialValue 7 0) (clock 0) =
    .cons (some ⟨7⟩) (.cons (some ⟨0⟩) .nil) :=
  factorialPreserves 7 0 ⟨carry 7 0, factorialExec 7 0, rfl⟩

private noncomputable def automatic {params : List (Ty Unit)} {t : Ty Unit}
    (p : WhileProgram Op params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  (p.translate .not).observe model
    ((p.translate .not).denote model input (p.translate_demandWellFounded .not)) (clock 0)

private theorem factorialCompiled (acc n : Nat) :
    automatic factorial (carry acc n) = .cons (some ⟨falling acc n⟩) .nil :=
  factorial.translate_returns .not model (carry acc n) (fun _ => rfl)
    ⟨carry (falling acc n) 0, factorialExec acc n, rfl⟩ (clock 0)

example : automatic factorial (carry 1 10) = .cons (some ⟨3628800⟩) .nil :=
  factorialCompiled 1 10

example : automatic factorial (carry 7 0) = .cons (some ⟨7⟩) .nil :=
  factorialCompiled 7 0

/-- The guard and the body make independent choices. The unchosen body arm
applies a primitive that always fails. -/
private def branchingLoop : WhileProgram Op [.count, .count] .count where
  guard := factorialGuard
  body := .branch (.op .positive (.cons (.var .head) .nil)) factorialBody
    (.seq (.assign (.op .bad .nil))
      (.project (.cons (.tail .head) (.cons (.tail (.tail .head)) .nil))))
  retvar := .head

private theorem branchingReturns : branchingLoop.source.Returns model (carry 2 1) ⟨2⟩ := by
  refine ⟨carry 2 0, ?_, rfl⟩
  exact .whileStep rfl (.branchTrue rfl (factorialStep 2 0)) (.whileStop rfl)

example : automatic branchingLoop (carry 2 1) = .cons (some ⟨2⟩) .nil :=
  branchingLoop.translate_returns .not model (carry 2 1) (fun _ => rfl) branchingReturns (clock 0)

example : branchingLoop.source.Fails model (carry 0 1) :=
  .whileBodyFailed rfl (.branchFalse rfl (.firstFailed (.assignFailed rfl)))

example : factorial.rank.check (factorial.translate .not) = true := by decide
example : (branchingLoop.translate .not).WellFormed := branchingLoop.translate_wellFormed .not

private noncomputable def structured {params : List (Ty Unit)} {t : Ty Unit}
    (p : Program Op true params t) (input : Tuple model.Value params) :
    Tuple (fun ty => Option (model.Value ty)) [t] :=
  let g := Structured.translate p .not
  g.observe model (g.denote model input (Structured.translate_demandWellFounded p .not)) (fun _ => 17)

/-- The second while is selected by a branch and initialized using the first
while's exit. The alternative contains a failing primitive. -/
private def siblingLoops : Program Op true [.count, .count] .count where
  locals := [.count, .count]
  body := .seq factorial.source.body
    (.branch (.op .positive (.cons (.var .head) .nil))
      (.seq (.project (.cons .head (.cons .head .nil))) factorial.source.body)
      (.seq (.assign (.op .bad .nil))
        (.project (.cons (.tail .head) (.cons (.tail (.tail .head)) .nil)))))
  retvar := .head

private theorem siblingReturns : siblingLoops.Returns model (carry 1 3) ⟨4320⟩ := by
  refine ⟨carry 4320 0, ?_, rfl⟩
  exact .seq (next := carry 6 0) (factorialExec 1 3)
    (.branchTrue rfl (.seq (next := carry 6 6) .project (factorialExec 6 6)))

example : structured siblingLoops (carry 1 3) = .cons (some ⟨4320⟩) .nil :=
  Structured.translate_returns siblingLoops .not model (carry 1 3) (fun _ => rfl)
    siblingReturns (fun _ => 17)

private def triple (acc outer inner : Nat) : Tuple model.Value [.count, .count, .count] :=
  .cons ⟨acc⟩ (.cons ⟨outer⟩ (.cons ⟨inner⟩ .nil))

private def innerTest : Expr Op [.count, .count, .count] .bool :=
  .op .positive (.cons (.var (.tail (.tail .head))) .nil)

private def innerBody : Stmt Op true [.count, .count, .count] [.count, .count, .count] :=
  .seq (.assign (.op .add (.cons (.var .head) (.cons (.var (.tail (.tail .head))) .nil))))
    (.seq (.assign (.op .pred (.cons (.var (.tail (.tail (.tail .head)))) .nil)))
      (.project (.cons (.tail .head) (.cons (.tail (.tail (.tail .head))) (.cons .head .nil)))))

private def innerLoop : Stmt Op true [.count, .count, .count] [.count, .count, .count] :=
  .while rfl innerTest innerBody

private def innerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => innerResult (acc + (k + 1)) k

private theorem innerExec (acc outer k : Nat) :
    Exec model innerLoop (triple acc outer k) (some (triple (innerResult acc k) outer 0)) := by
  induction k generalizing acc with
  | zero => exact .whileStop rfl
  | succ k ih =>
    apply Exec.whileStep (next := triple (acc + (k + 1)) outer k) rfl ?_ (ih _)
    exact .seq (next := prependCount (acc + (k + 1)) (triple acc outer (k + 1))) (.assign rfl)
      (.seq (next := prependCount k (prependCount (acc + (k + 1)) (triple acc outer (k + 1))))
        (.assign rfl) .project)

private def outerTest : Expr Op [.count, .count, .count] .bool :=
  .op .positive (.cons (.var (.tail .head)) .nil)

private def outerBody : Stmt Op true [.count, .count, .count] [.count, .count, .count] :=
  .seq (.project (.cons .head (.cons (.tail .head) (.cons (.tail .head) .nil))))
    (.seq innerLoop
      (.seq (.assign (.op .pred (.cons (.var (.tail .head)) .nil)))
        (.project (.cons (.tail .head) (.cons .head (.cons (.tail (.tail (.tail .head))) .nil))))))

private def outerResult (acc : Nat) : Nat → Nat
  | 0 => acc
  | k + 1 => outerResult (innerResult acc (k + 1)) k

private theorem outerExec (acc k : Nat) :
    Exec model (.while rfl outerTest outerBody) (triple acc k 0)
      (some (triple (outerResult acc k) 0 0)) := by
  induction k generalizing acc with
  | zero => exact .whileStop rfl
  | succ k ih =>
    apply Exec.whileStep (next := triple (innerResult acc (k + 1)) k 0) rfl ?_ (ih _)
    exact .seq (next := triple acc (k + 1) (k + 1)) .project
      (.seq (next := triple (innerResult acc (k + 1)) (k + 1) 0) (innerExec acc (k + 1) (k + 1))
        (.seq (next := prependCount k (triple (innerResult acc (k + 1)) (k + 1) 0))
          (.assign rfl) .project))

/-- The inner loop's trip count is the current outer counter. For an outer
input of three the inner exits occur at three, two and one, respectively. -/
private def nestedLoops : Program Op true [.count, .count, .count] .count where
  locals := [.count, .count, .count]
  body := .while rfl outerTest outerBody
  retvar := .head

example (acc n : Nat) : structured nestedLoops (triple acc n 0) =
    .cons (some ⟨outerResult acc n⟩) .nil :=
  Structured.translate_returns nestedLoops .not model (triple acc n 0) (fun _ => rfl)
    ⟨triple (outerResult acc n) 0 0, outerExec acc n, rfl⟩ (fun _ => 17)

example : structured nestedLoops (triple 0 3 0) = .cons (some ⟨10⟩) .nil :=
  Structured.translate_returns nestedLoops .not model (triple 0 3 0) (fun _ => rfl)
    ⟨triple 10 0 0, outerExec 0 3, rfl⟩ (fun _ => 17)

private def passParents {params : List (Ty Unit)} (p : Program Op true params .count) :
    List (Nat × Option Nat) :=
  let g := Structured.translate p .not
  (List.finRange (Structured.program p .not).nodes.length).filterMap fun i =>
    (Structured.passLoop (g.node i).label).map fun loop =>
      (loop.val, (g.forest.parent loop).map Fin.val)

#guard match passParents siblingLoops with
  | [(a, none), (b, none)] => a < b
  | _ => False

#guard match passParents nestedLoops with
  | [(outer, none), (inner, some parent)] => parent = outer ∧ outer < inner
  | _ => False

-- The structural admission also supplies existence and uniqueness for the
-- graph whose inner trip count changes with the enclosing iteration.
example :
    ∃! value, (Structured.translate nestedLoops .not).Solves model (triple 0 3 0) value :=
  (Structured.translate nestedLoops .not).existsUnique_solves_of_wellFormed model (triple 0 3 0)
    (Structured.translate_wellFormed nestedLoops .not)

example : (Structured.translate siblingLoops .not).Scoped :=
  (Structured.translate_wellFormed siblingLoops .not).loopScope

example : (Structured.translate nestedLoops .not).OuterFeedbackCycles :=
  (Structured.translate_wellFormed nestedLoops .not).outerFeedback

private def nestedIdentity : Program Op true [.bool] .bool where
  locals := [.bool]
  body := .while rfl (.var .head)
    (.while rfl (.var .head) (.project (.cons .head .nil)))
  retvar := .head

private def nestedId (i : Fin 9) : Fin (Structured.program nestedIdentity .not).nodes.length := i

/-- The outer θ depends on the inner exit. This cycle traverses the
inner eval's index edge and the shared pass. -/
private theorem nestedIndexCycle :
    let g := Structured.translate nestedIdentity .not
    Walk g.Edge (nestedId 7)
      [.feedback (nestedId 1), .index (nestedId 4), .sample (nestedId 4),
        .ordinary, .initial (nestedId 4)] (nestedId 7) := by
  dsimp only
  refine .cons (b := nestedId 3) ⟨⟨1, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 4) ⟨⟨1, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 5) ⟨⟨0, by decide⟩, rfl, rfl⟩ ?_
  refine .cons (b := nestedId 6) ⟨⟨0, by decide⟩, rfl, rfl⟩ ?_
  exact .cons ⟨⟨0, by decide⟩, rfl, rfl⟩ (.nil _)

example : (Structured.translate nestedIdentity .not).forest.StrictlyEncloses (nestedId 1) (nestedId 4) := by
  have wf := Structured.translate_wellFormed nestedIdentity .not
  obtain ⟨outer, encloses, feedback⟩ := wf.outerFeedback _ _ nestedIndexCycle
    (.index (nestedId 4)) (by simp) (nestedId 4) (.inr rfl)
  have onlyOuter : outer = nestedId 1 := by simpa using feedback
  rwa [onlyOuter] at encloses

end Silmaril.SSA.PEG.Simple.Tests

namespace Silmaril.SSA.PEG.Simple.Structured.Completion.Tests

open RVSDG (Tuple)
open Rules (readRef)

set_option backward.isDefEq.respectTransparency false

private inductive Op : InstructionSet Unit
  | positive : Op [.count] .bool
  | not : Op [.bool] .bool
  | pred : Op [.count] .count
  | probe : Op [.bool] .count

private def model : Interpretation Op where
  carrier _ := Unit
  run
    | .positive, .cons x .nil => some ⟨decide (0 < x.down)⟩
    | .not, .cons x .nil => some ⟨!x.down⟩
    | .pred, .cons x .nil => some ⟨x.down - 1⟩
    | .probe, .cons x .nil => if x.down then some ⟨0⟩ else none

private abbrev vars : List (Ty Unit) := [.count, .bool]

private def guard : Expr Op vars .bool := .op .positive (.cons (.var .head) .nil)

/-- The old counter feeds its update. The result of the strict probe is discarded. -/
private def body : Stmt Op false vars vars :=
  .seq (.assign (.op .probe (.cons (.var (.tail .head)) .nil)))
    (.seq (.assign (.op .pred (.cons (.var (.tail .head)) .nil)))
      (.project (.cons .head (.cons (.tail (.tail (.tail .head))) .nil))))

private def source := whileProgram guard body.enableWhile .head
private def graph : Graph Op vars [.count] 11 11 := translate source .not
private def input (count : Nat) (permit : Bool) : Tuple model.Value vars :=
  .cons ⟨count⟩ (.cons ⟨permit⟩ .nil)

private def key : Fin 11 := 2
private def base : Index 11 := fun _ => 0
private def sample (k : Nat) : Index 11 := base.set key k

private theorem setSample (a b : Nat) : (sample a).set key b = sample b := by
  funext j
  by_cases h : j = key <;> simp [sample, Index.set, h]

private def r (i : Fin 11) {t : Ty Unit} (typed : graph.sort i = t) : Ref graph.sort t :=
  ⟨i, typed⟩

private noncomputable def values (n : Nat) (permit : Bool) : graph.Valuation model :=
  graph.denote model (input n permit) (translate_demandWellFounded source .not)

private theorem solved (n : Nat) (permit : Bool) :
    graph.Solves model (input n permit) (values n permit) :=
  graph.denote_solves model (input n permit) _

-- Compute the live loop from the compiler's equations, independently of
-- source execution and for either value of the discarded probe's input.
private theorem countdown (n : Nat) (permit : Bool) (k : Nat) :
    readRef (values n permit) (r 7 (t := .count) rfl) (sample k) = some ⟨n - k⟩ := by
  have eq := solved n permit
  induction k with
  | zero =>
    rw [Rules.theta_zero eq (r := r 7 (t := .count) rfl) (initial := r 9 rfl) (feedback := r 4 rfl)
      (loop := key) HEq.rfl rfl]
    exact Rules.at_label eq (r := r 9 rfl) (label := .param .head) (args := .nil) HEq.rfl _
  | succ k ih =>
    rw [Rules.theta_succ eq (r := r 7 (t := .count) rfl) (initial := r 9 rfl) (feedback := r 4 rfl)
      (loop := key) HEq.rfl rfl,
      setSample, Rules.unary_at eq (r := r 4 rfl) (arg := r 7 rfl) (op := Op.pred) HEq.rfl, ih]
    change some (ULift.up (n - k - 1)) = some (ULift.up (n - (k + 1)))
    congr 2

private theorem exitFlag (n : Nat) (permit : Bool) (j : Nat) :
    readRef (values n permit) (r 3 rfl) (sample j) = some ⟨decide (n ≤ j)⟩ := by
  have eq := solved n permit
  rw [Rules.unary_at eq (r := r 3 rfl) (arg := r 6 rfl) (op := Op.not) HEq.rfl,
    Rules.unary_at eq (r := r 6 rfl) (arg := r 7 rfl) (op := Op.positive) HEq.rfl, countdown]
  change some (ULift.up (!decide (0 < n - j))) = some (ULift.up (decide (n ≤ j)))
  by_cases h : n ≤ j
  · simp [h, Nat.sub_eq_zero_of_le h]
  · have pos : 0 < n - j := by omega
    simp [h, pos]

private theorem firstPass (n : Nat) (permit : Bool) :
    readWhilePass guard body.enableWhile .head .not model (values n permit) base =
      some ⟨n⟩ := by
  change readRef (values n permit) (r 2 (t := .count) rfl) base = _
  rw [Rules.pass_at (solved n permit) (r := r 2 rfl) (cond := r 3 rfl) (loop := key) HEq.rfl]
  have stream : (fun j => (readRef (values n permit) (r 3 rfl) (sample j)).map ULift.down) =
      fun j => some (decide (n ≤ j)) := by
    funext j
    rw [exitFlag]
    rfl
  change (firstTrue (fun j => (readRef (values n permit) (r 3 rfl) (sample j)).map ULift.down)).map
    ULift.up = _
  have first : firstTrue (fun j => some (decide (n ≤ j))) = some n :=
    (firstTrue_eq_some_iff_samples _ n).mpr ⟨by simp, fun j lt => by simp [Nat.not_le_of_lt lt]⟩
  rw [stream, first]
  rfl

private theorem observed (n : Nat) (permit : Bool) :
    graph.observe model (values n permit) base = .cons (some ⟨0⟩) .nil := by
  have pass := firstPass n permit
  change readRef (values n permit) (r 2 (t := .count) rfl) base = _ at pass
  have evaluated := Rules.eval_at (solved n permit) (r := r 0 rfl) (source := r 7 rfl)
    (count := r 2 rfl) (loop := key) HEq.rfl base
  rw [pass] at evaluated
  change readRef (values n permit) (r 0 rfl) base =
    monotonize (fun j => readRef (values n permit) (r 7 rfl) (sample j)) n at evaluated
  have result := (monotonize_eq_some_iff
    (fun j => readRef (values n permit) (r 7 (t := .count) rfl) (sample j)) n (ULift.up 0)).mpr
    ⟨by rw [countdown, Nat.sub_self], fun j _ => by rw [countdown]; rfl⟩
  change Tuple.cons (F := fun t => Option (model.Value t)) (t := .count)
    (readRef (values n permit) (r 0 rfl) base) .nil = _
  rw [evaluated, result]

#guard checkWhilePrefix model guard body 2 (input 2 true)
#guard !checkWhilePrefix model guard body 2 (input 2 false)
#guard checkWhilePrefix model guard body 0 (input 0 false)

private theorem returnsFromPEG {n : Nat} {permit : Bool}
    (checked : checkWhilePrefix model guard body n (input n permit) = true) :
    source.Returns model (input n permit) ⟨0⟩ :=
  translate_while_returns_of_checkedPrefix guard body .head .not
    model (input n permit) (fun _ => rfl) base (firstPass n permit) checked (observed n permit)

example : source.Returns model (input 2 true) ⟨0⟩ := returnsFromPEG rfl
example : source.Returns model (input 0 false) ⟨0⟩ := returnsFromPEG rfl

private theorem fails : source.Fails model (input 2 false) :=
  .whileBodyFailed rfl (.firstFailed (.assignFailed rfl))

/-- A defined first pass and return survive the discarded probe's failure.
Figure 11's value observation alone cannot give a successful source run. -/
example : graph.observe model (values 2 false) base = .cons (some ⟨0⟩) .nil ∧
    readWhilePass guard body.enableWhile .head .not model (values 2 false) base = some ⟨2⟩ ∧
    ¬ source.Returns model (input 2 false) ⟨0⟩ := by
  refine ⟨observed 2 false, firstPass 2 false, ?_⟩
  rintro ⟨_, run, _⟩
  cases fails.deterministic run

end Silmaril.SSA.PEG.Simple.Structured.Completion.Tests
