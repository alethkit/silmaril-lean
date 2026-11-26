module

import Silmaril.SSA.PEG.Simple.Thms
import Silmaril.SSA.PEG.Thms

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
private def factorialBody : Stmt Op true [.count, .count] [.count, .count] :=
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
    Exec model factorialBody (carry acc (n + 1)) (some (carry (acc * (n + 1)) n)) :=
  .seq (next := prependCount (acc * (n + 1)) (carry acc (n + 1))) (.assign rfl)
    (.seq (next := prependCount n (prependCount (acc * (n + 1)) (carry acc (n + 1))))
      (.assign rfl) .project)

private theorem factorialExec (acc n : Nat) :
    Exec model (.while rfl factorialGuard factorialBody) (carry acc n)
      (some (carry (falling acc n) 0)) := by
  induction n generalizing acc with
  | zero => exact .whileStop rfl
  | succ n ih => exact .whileStep rfl (factorialStep acc n) (ih (acc * (n + 1)))

private def factorial : Program Op true [.count, .count] .count where
  locals := [.count, .count]
  body := .while rfl factorialGuard factorialBody
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
    (run : factorial.Returns model (carry acc n) value) :
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

end Silmaril.SSA.PEG.Simple.Tests
