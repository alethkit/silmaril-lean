module

import Silmaril.SSA.PEG.Thms

namespace Silmaril.SSA.PEG.Tests

open RVSDG (Tuple)

private inductive Op : List (Ty Unit) → Ty Unit → Type where
  | zero : Op [] .count
  | one : Op [] .count
  | add : Op [.count, .count] .count
  | alternateAdd : Op [.count, .count] .count

private def mergeAdd : InstructionMap Op Op
  | _, _, .alternateAdd => .add
  | _, _, instr => instr

/-- Vertex 0 is the result of a conditional. The add uses the same
producer twice, and the roots repeat one output. -/
private def diamond : RawGraph Op [.bool] [.count, .count, .bool] 5 0 where
  forest := ⟨Fin.elim0⟩
  sort i := if i = 1 then .bool else .count
  node i := match i with
    | 0 => ⟨_, .phi, [1, 3, 4]⟩
    | 1 => ⟨_, .param .head, []⟩
    | 2 => ⟨_, .op .one, []⟩
    | 3 => ⟨_, .op .alternateAdd, [2, 2]⟩
    | 4 => ⟨_, .op .zero, []⟩
  roots := [0, 0, 1]

example : diamond.check.isSome = true := by decide
example : ({ diamond with roots := [0, 0, 5] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide
example : ({ diamond with roots := [0, 0, 2] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide
example : ({ diamond with roots := [0, 0] } : RawGraph Op [.bool] [.count, .count, .bool] 5 0).check.isNone = true :=
  by decide

private def typedDiamond : Graph Op [.bool] [.count, .count, .bool] 5 0 :=
  diamond.check.get (by decide)

example : refNumbers (typedDiamond.node 3).args = [2, 2] := by decide
example : refNumbers typedDiamond.roots = [0, 0, 1] := by decide

example : (checkRefs diamond.sort [.bool, .count, .count] [1, 3]).isNone = true := by decide
example : (checkRefs diamond.sort [.bool, .count, .count] [2, 3, 4]).isNone = true := by decide

example : ∃ op, ((typedDiamond.mapOps mergeAdd).node 3).label = .op op ∧
    refNumbers ((typedDiamond.mapOps mergeAdd).node 3).args = [2, 2] :=
  ⟨.add, rfl, rfl⟩

private def loops : LoopForest 2 :=
  ⟨fun i => if i = 1 then some 0 else none⟩

private def countRef (i : Fin 5) : Ref (fun _ : Fin 5 => (Ty.count : Ty Unit)) .count := ⟨i, rfl⟩

private def pair (a b : Fin 5) : Tuple (Ref (fun _ : Fin 5 => (Ty.count : Ty Unit))) [.count, .count] :=
  .cons (countRef a) (.cons (countRef b) .nil)

/-- A (0), E (1), B (2), zero (3), one (4). Put E in A's feedback or initial slot. -/
private def nested (outerFeedback : Bool) : Graph Op [] [.count] 5 2 where
  forest := loops
  sort _ := .count
  node i := match i with
    | 0 => .ofLabel (.theta 0) (if outerFeedback then pair 3 1 else pair 1 3)
    | 1 => .ofLabel (.eval 1) (pair 2 4)
    | 2 => .ofLabel (.theta 1) (pair 3 0)
    | 3 => .ofLabel (.op .zero) .nil
    | 4 => .ofLabel (.op .one) .nil
  roots := .cons (countRef 0) .nil

private theorem validForest : loops.WellFormed := by
  intro i
  rintro ⟨ks, path, pos⟩
  have step : ∀ (a b : Fin 2), loops.Up a () b → b.val < a.val := by
    unfold LoopForest.Up
    decide
  exact (Nat.lt_irrefl i.val) (path.strictRank pos Fin.val (fun e _ => step _ _ e))

private theorem outerAncestor : loops.StrictlyEncloses 0 1 :=
  ⟨[()], .cons (by rfl) (.nil 0), by decide⟩

/-- Check a local edge property by enumerating the operand slots of the five vertices. -/
private theorem forEdges {feedback : Bool} {p : Fin 5 → EdgeKind (Fin 2) → Fin 5 → Prop}
    (check : ∀ a i, p a (((nested feedback).node a).label.kind i)
        (((nested feedback).node a).arg i).id) :
    ∀ {a b k}, (nested feedback).Edge a k b → p a k b := by
  rintro a b k ⟨i, rfl, rfl⟩
  exact check a i

private def feedbackRank (i : Fin 5) : Nat :=
  match i with
  | 0 => 3 | 1 => 2 | 2 => 1 | _ => 0

private theorem feedbackCycles (back : Bool) : (nested back).FeedbackCycles := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      ¬k.IsFeedback → feedbackRank b < feedbackRank a := by
    cases back
    all_goals
      apply forEdges
      decide
  intro a ks path pos
  by_cases h : ∃ k ∈ ks, k.IsFeedback
  · exact h
  · exact (Nat.lt_irrefl _ (path.strictRank pos feedbackRank
      (fun e hk => step e (fun hb => h ⟨_, hk, hb⟩)))).elim

private theorem loopScope (back : Bool) : (nested back).Scoped := by
  have startAt : ∀ a, ((nested back).node a).label.loop = some 0 → a ≠ 2 := by
    cases back <;> decide
  have endsAt : ∀ b, ((nested back).node b).label.thetaLoop = some 1 → b = 2 := by
    cases back <;> decide
  have step : ∀ {a b k}, (nested back).Edge a k b → b = 2 → k = .sample 1 := by
    cases back
    all_goals
      apply forEdges
      decide
  intro a b ks start target path ha hb
  by_cases eq : target = start
  · subst target
    exact .inl ⟨[], .nil _⟩
  by_cases st : start = 1
  · have tg : target = 0 := by
      apply Fin.ext
      have := target.isLt
      omega
    subst start
    subst target
    obtain ⟨es, ancestry, _⟩ := outerAncestor
    exact .inl ⟨es, ancestry⟩
  · have st0 : start = 0 := Fin.ext (by omega)
    have tg1 : target = 1 := Fin.ext (by omega)
    subst start
    subst target
    right
    by_cases sampled : EdgeKind.sample (1 : Fin 2) ∈ ks
    · exact sampled
    · have avoid := path.preserves (p := fun a => a ≠ 2)
        (fun e hk _ eq => sampled (step e eq ▸ hk)) (startAt a ha)
      exact (avoid (endsAt b hb)).elim

private def outerRole (back : Bool) : EdgeKind (Fin 2) :=
  if back then .feedback 0 else .initial 0

private def outerRank (i : Fin 5) : Nat :=
  match i with
  | 0 => 1 | 1 => 3 | 2 => 2 | _ => 0

private theorem everyCycleVisitsOuter (back : Bool) {a : Fin 5} {ks : List (EdgeKind (Fin 2))}
    (path : Walk (nested back).Edge a ks a) (pos : ks ≠ []) : outerRole back ∈ ks := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      k ≠ outerRole back → outerRank b < outerRank a := by
    cases back
    all_goals
      apply forEdges
      decide
  by_cases h : outerRole back ∈ ks
  · exact h
  · exact (Nat.lt_irrefl _ (path.strictRank pos outerRank
      (fun e hk => step e (fun eq => h (eq ▸ hk))))).elim

private theorem observerIsInner {back : Bool} {a b : Fin 5} {ks : List (EdgeKind (Fin 2))}
    (path : Walk (nested back).Edge a ks b) :
    ∀ k ∈ ks, ∀ l, k.IsObserverAt l → l = 1 := by
  have step : ∀ {a b k}, (nested back).Edge a k b →
      ∀ l, k.IsObserverAt l → l = 1 := by
    cases back
    all_goals
      apply forEdges
      unfold EdgeKind.IsObserverAt
      decide
  induction path with
  | nil => simp
  | cons edge _ ih =>
    intro k hk l hl
    rcases List.mem_cons.mp hk with rfl | tail
    · exact step edge l hl
    · exact ih k tail l hl

private theorem strong : (nested true).WellFormed where
  forest := validForest
  feedback := feedbackCycles true
  loopScope := loopScope true
  outerFeedback := by
    intro a ks path k hk inner obs
    have hi := observerIsInner path k hk inner obs
    subst inner
    exact ⟨0, outerAncestor, everyCycleVisitsOuter true path (by intro eq; simp [eq] at hk)⟩

private theorem weak : (nested false).PaperWellFormed where
  forest := validForest
  feedback := feedbackCycles false
  loopScope := loopScope false
  outerTheta := by
    intro a ks path k hk inner obs
    have hi := observerIsInner path k hk inner obs
    subst inner
    exact ⟨0, outerAncestor, .initial 0,
      everyCycleVisitsOuter false path (by intro eq; simp [eq] at hk), .inl rfl⟩

private theorem weakCycle : Walk (nested false).Edge 0 [.initial 0, .sample 1, .feedback 1] 0 :=
  .cons (show (nested false).Edge 0 (.initial 0) 1 from ⟨⟨0, by decide⟩, rfl, rfl⟩)
    (.cons (show (nested false).Edge 1 (.sample 1) 2 from ⟨⟨0, by decide⟩, rfl, rfl⟩)
      (.cons (show (nested false).Edge 2 (.feedback 1) 0 from ⟨⟨1, by decide⟩, rfl, rfl⟩) (.nil 0)))

example : (nested false).PaperWellFormed ∧ ¬(nested false).WellFormed := by
  refine ⟨weak, fun h => ?_⟩
  obtain ⟨outer, above, onCycle⟩ := h.outerFeedback 0 _ weakCycle _ (by decide) 1 (.inl rfl)
  have houter : outer = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at onCycle
    obtain h | h | h := onCycle
    · cases h
    · cases h
    · cases h
      rfl
  exact validForest 1 (houter ▸ above)

/-- Two top-level loops. A direct reference into the sibling's θ is out of scope. -/
private def siblings : Graph Op [] [.count] 5 2 where
  forest := ⟨fun _ => none⟩
  sort _ := .count
  node i := if i = 0 then .ofLabel (.theta 0) (pair 3 2) else (nested true).node i
  roots := .cons (countRef 0) .nil

example : ¬siblings.Scoped := by
  intro scopedGraph
  have edge : siblings.Edge 0 (.feedback 0) 2 := ⟨⟨1, by decide⟩, rfl, rfl⟩
  rcases scopedGraph 0 2 [.feedback 0] 0 1 (.cons edge (.nil 2)) rfl rfl with above | sampled
  · obtain ⟨ks, ancestry⟩ := above
    cases ancestry with
    | cons up _ => contradiction
  · exact (by decide : EdgeKind.sample (1 : Fin 2) ∉ [EdgeKind.feedback 0]) sampled

private def swapTwo : Fin 2 ≃ Fin 2 where
  toFun i := if i = 0 then 1 else 0
  invFun i := if i = 0 then 1 else 0
  left_inv := by unfold Function.LeftInverse; decide
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide

private def reverseFive : Fin 5 ≃ Fin 5 where
  toFun i := ⟨4 - i.val, by omega⟩
  invFun i := ⟨4 - i.val, by omega⟩
  left_inv := by unfold Function.LeftInverse; decide
  right_inv := by unfold Function.RightInverse Function.LeftInverse; decide

example : ((nested true).reindex reverseFive swapTwo).WellFormed :=
  ((nested true).wellFormed_reindex reverseFive swapTwo).mpr strong

example : ((nested true).reindex reverseFive swapTwo).Edge 4 (.feedback 1) 3 :=
  ((nested true).edge_relabel (fun op => op) reverseFive swapTwo 4 3 (.feedback 1)).mpr
    ⟨⟨1, by decide⟩, rfl, rfl⟩

/-- Specialized Fig. 11 equations for the weak graph, in outer/inner index
order. E samples at index 1, so monotonize checks exactly the prefix at 0. -/
private def SolvesWeak (a e b : Nat → Nat → Option Nat) : Prop :=
  (∀ o i, a o i = if o = 0 then e o i else some 0) ∧
  (∀ o i, e o i = if b o 0 = none then none else b o 1) ∧
  (∀ o i, b o i = if i = 0 then some 0 else a o (i - 1))

private def valueA (k o _i : Nat) : Option Nat :=
  if o = 0 then some k else some 0

private def valueB (k o i : Nat) : Option Nat :=
  if i = 0 then some 0 else valueA k o (i - 1)

private theorem solves (k : Nat) : SolvesWeak (valueA k) (valueA k) (valueB k) := by
  refine ⟨?_, ?_, fun _ _ => rfl⟩
  · intro o i
    by_cases h : o = 0 <;> simp [valueA, h]
  · intro o i
    simp [valueA, valueB]

example : ∃ a e b a' e' b', SolvesWeak a e b ∧ SolvesWeak a' e' b' ∧ a 0 0 ≠ a' 0 0 :=
  ⟨valueA 0, valueA 0, valueB 0, valueA 1, valueA 1, valueB 1,
    solves 0, solves 1, by decide⟩

end Silmaril.SSA.PEG.Tests
