module

public import Silmaril.SSA.PEG.Bridge.Theta.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Proofs

open RVSDG (Tuple)

variable {Data : Type} {P : InstructionSet.{0,0} Data} {a b : Ty Data}

theorem rank_check (loop : Loop P a b) : rank.check loop.peg = true := rfl

theorem stateAt_succ (loop : Loop P a b) (m : TotalModel P)
    (input : Tuple m.toPEG.Value [a, b]) (k : Nat) :
    loop.stateAt m (k + 1) input = loop.advance m (loop.stateAt m k input) := by
  induction k generalizing input with
  | zero => rfl
  | succ k ih => exact ih (loop.advance m input)

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem set_clock (idx : Index 1) (k : Nat) : idx.set 0 k = clock k := by
  funext i
  have zero : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst i
  rfl

private theorem collect_pair {F : Ty Data → Type}
    (read : ∀ s : Fin ([a, b] : List (Ty Data)).length, Option (F [a, b][s]))
    (xs : Tuple F [a, b]) (left : read 0 = some (xs.get .head))
    (right : read 1 = some (xs.get (.tail .head))) :
    collect (F := F) [a, b] read = some xs := by
  have readers : read = (fun i => some (xs.get (portAt [a, b] i))) := by
    funext i
    have positions : i = 0 ∨ i = 1 := by
      have bound := i.isLt
      change i.val < 2 at bound
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases positions with rfl | rfl
    · exact left
    · exact right
  rw [readers]
  cases xs with
  | cons x tail =>
    cases tail with
    | cons y tail => cases tail; rfl

private theorem run_pair (m : TotalModel P) {t : Ty Data} (op : P [a, b] t)
    (read : ∀ s : Fin ([a, b] : List (Ty Data)).length, Option (m.toPEG.Value [a, b][s]))
    (xs : Tuple m.toPEG.Value [a, b]) (left : read 0 = some (xs.get .head))
    (right : read 1 = some (xs.get (.tail .head))) :
    (collect (F := m.toPEG.Value) [a, b] read).elim none (m.toPEG.run op) =
      some (m.run op xs) :=
  congrArg (fun values : Option (Tuple m.toPEG.Value [a, b]) => values.elim none (m.toPEG.run op))
    (collect_pair read xs left right)

private theorem monotonize_defined {X : Type} (stream : Nat → X) (k : Nat) :
    monotonize (fun j => some (stream j)) k = some (stream k) :=
  (monotonize_eq_some_iff _ _ _).mpr ⟨rfl, fun _ _ => rfl⟩

variable (loop : Loop P a b) (m : TotalModel P) (input : Tuple m.toPEG.Value [a, b])
variable (wf : WellFounded loop.peg.Demand)

private noncomputable abbrev val : loop.peg.Valuation m.toPEG :=
  loop.peg.denote m.toPEG input wf

private theorem equation (q : Request 10 1) :
    val loop m input wf q = loop.peg.equation m.toPEG input (val loop m input wf) q :=
  loop.peg.denote_solves m.toPEG input wf q

private theorem carried_at (k : Nat) :
    val loop m input wf (2, clock k) = some ((loop.stateAt m k input).get .head) ∧
    val loop m input wf (3, clock k) = some ((loop.stateAt m k input).get (.tail .head)) := by
  induction k with
  | zero =>
    exact ⟨(equation loop m input wf (2, clock 0)).trans (equation loop m input wf (0, clock 0)),
      (equation loop m input wf (3, clock 0)).trans (equation loop m input wf (1, clock 0))⟩
  | succ k ih =>
    obtain ⟨left, right⟩ := ih
    let xs := loop.stateAt m k input
    have nextLeft : val loop m input wf (6, clock k) = some (m.run loop.nextLeft xs) := by
      refine (equation loop m input wf (6, clock k)).trans ?_
      change (collect (F := m.toPEG.Value) [a, b] _).elim none (m.toPEG.run loop.nextLeft) = _
      exact run_pair m loop.nextLeft _ xs left right
    have nextRight : val loop m input wf (7, clock k) = some (m.run loop.nextRight xs) := by
      refine (equation loop m input wf (7, clock k)).trans ?_
      change (collect (F := m.toPEG.Value) [a, b] _).elim none (m.toPEG.run loop.nextRight) = _
      exact run_pair m loop.nextRight _ xs left right
    have thetaLeft := equation loop m input wf (2, clock (k + 1))
    have thetaRight := equation loop m input wf (3, clock (k + 1))
    change val loop m input wf (2, clock (k + 1)) =
      val loop m input wf (6, (clock (k + 1)).set 0 k) at thetaLeft
    change val loop m input wf (3, clock (k + 1)) =
      val loop m input wf (7, (clock (k + 1)).set 0 k) at thetaRight
    rw [set_clock, nextLeft] at thetaLeft
    rw [set_clock, nextRight] at thetaRight
    rw [stateAt_succ]
    exact ⟨thetaLeft, thetaRight⟩

private theorem stop_at (k : Nat) :
    val loop m input wf (4, clock k) = some (m.run loop.stop (loop.stateAt m k input)) := by
  obtain ⟨left, right⟩ := carried_at loop m input wf k
  refine (equation loop m input wf (4, clock k)).trans ?_
  change (collect (F := m.toPEG.Value) [a, b] _).elim none (m.toPEG.run loop.stop) = _
  exact run_pair m loop.stop _ _ left right

private noncomputable abbrev passCount (idx : Index 1) : Option (ULift Nat) :=
  val loop m input wf (5, idx)

private theorem pass (idx : Index 1) :
    passCount loop m input wf idx =
      (firstTrue (fun j => some (loop.exits m (loop.stateAt m j input)))).map ULift.up := by
  have eq := equation loop m input wf (5, idx)
  change val loop m input wf (5, idx) =
    (firstTrue (fun j => (val loop m input wf (4, idx.set 0 j)).map ULift.down)).map ULift.up at eq
  have stream :
      (fun j => (val loop m input wf (4, idx.set 0 j)).map ULift.down) =
        fun j => some (loop.exits m (loop.stateAt m j input)) := by
    funext j
    rw [set_clock, stop_at]
    rfl
  rw [stream] at eq
  exact eq

theorem pass_eq_some_iff (idx : Index 1) (k : Nat) :
    (loop.peg.denote m.toPEG input wf) (5, idx) = some ⟨k⟩ ↔ loop.FirstExit m input k := by
  change passCount loop m input wf idx = some (ULift.up k) ↔ _
  rw [pass loop m input wf idx]
  have index :
      (firstTrue (fun j => some (loop.exits m (loop.stateAt m j input)))).map ULift.up =
        (some ⟨k⟩ : Option (ULift Nat)) ↔
        firstTrue (fun j => some (loop.exits m (loop.stateAt m j input))) = some k := by
    cases firstTrue (fun j => some (loop.exits m (loop.stateAt m j input))) with
    | none => simp
    | some n =>
      constructor
      · intro eq
        exact congrArg (Option.map ULift.down) eq
      · intro eq
        exact congrArg (Option.map ULift.up) eq
  rw [index, firstTrue_eq_some_iff]
  simp only [monotonize_defined, Option.some.injEq, Loop.FirstExit]
  constructor
  · intro h
    have eqFalse : ∀ x : Bool, x ≠ true → x = false := by decide
    exact ⟨h.1, fun j hj => eqFalse _ (fun eq => h.2 j hj (congrArg some eq))⟩
  · intro h
    refine ⟨h.1, fun j hj => ?_⟩
    rw [h.2 j hj]
    decide

private theorem roots (idx : Index 1) :
    loop.peg.observe m.toPEG (val loop m input wf) idx =
      match passCount loop m input wf idx with
      | none => .cons none (.cons none .nil)
      | some k => (loop.stateAt m k.down input).map (fun _ => some) := by
  have left := equation loop m input wf (8, idx)
  have right := equation loop m input wf (9, idx)
  change val loop m input wf (8, idx) =
    (passCount loop m input wf idx).elim none
      (fun k => monotonize (fun j => val loop m input wf (2, idx.set 0 j)) k.down) at left
  change val loop m input wf (9, idx) =
    (passCount loop m input wf idx).elim none
      (fun k => monotonize (fun j => val loop m input wf (3, idx.set 0 j)) k.down) at right
  have leftStream :
      (fun j => val loop m input wf (2, idx.set 0 j)) =
        fun j => some ((loop.stateAt m j input).get .head) := by
    funext j
    rw [set_clock]
    exact (carried_at loop m input wf j).1
  have rightStream :
      (fun j => val loop m input wf (3, idx.set 0 j)) =
        fun j => some ((loop.stateAt m j input).get (.tail .head)) := by
    funext j
    rw [set_clock]
    exact (carried_at loop m input wf j).2
  change Tuple.cons (F := fun t => Option (m.toPEG.Value t)) (t := a)
    (val loop m input wf (8, idx)) (.cons (t := b) (val loop m input wf (9, idx)) .nil) = _
  rw [left, right, leftStream, rightStream]
  cases passCount loop m input wf idx with
  | none => rfl
  | some k =>
    have hl := monotonize_defined (fun j => (loop.stateAt m j input).get .head) k.down
    have hr := monotonize_defined (fun j => (loop.stateAt m j input).get (.tail .head)) k.down
    refine (congrArg₂ (fun l r => Tuple.cons (F := fun t => Option (m.toPEG.Value t))
      (t := a) l (.cons (t := b) r .nil)) hl hr).trans ?_
    change _ = (loop.stateAt m k.down input).map (fun _ => some)
    cases loop.stateAt m k.down input with
    | cons x tail =>
      cases tail with
      | cons y tail => cases tail; rfl

theorem observe_firstExit (idx : Index 1) {k : Nat} (exit : loop.FirstExit m input k) :
    loop.peg.observe m.toPEG (loop.peg.denote m.toPEG input wf) idx =
      (loop.stateAt m k input).map (fun _ => some) := by
  have found : passCount loop m input wf idx = some (ULift.up k) :=
    (pass_eq_some_iff loop m input wf idx k).mpr exit
  rw [roots, found]

private theorem someTuple_injective {F : Ty Data → Type} {ts : List (Ty Data)}
    {xs ys : Tuple F ts} (eq : xs.map (fun _ => some) = ys.map (fun _ => some)) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys =>
      have head : some x = some y := congrArg (fun zs => zs.get .head) eq
      have tail : xs.map (fun _ => some) = ys.map (fun _ => some) :=
        congrArg (fun | .cons _ tail => tail) eq
      exact congrArg₂ Tuple.cons (Option.some.inj head) (ih tail)

theorem observe_iff (idx : Index 1) (output : Tuple m.toPEG.Value [a, b]) :
    loop.peg.observe m.toPEG (loop.peg.denote m.toPEG input wf) idx = output.map (fun _ => some) ↔
      ∃ k, loop.FirstExit m input k ∧ output = loop.stateAt m k input := by
  constructor
  · intro h
    rw [roots] at h
    cases found : passCount loop m input wf idx with
    | none =>
      rw [found] at h
      cases output with
      | cons x tail =>
        have bad : (none : Option (m.toPEG.Value a)) = some x :=
          congrArg (fun xs => xs.get .head) h
        contradiction
    | some k =>
      rw [found] at h
      exact ⟨k.down, (pass_eq_some_iff loop m input wf idx k.down).mp found,
        (someTuple_injective h).symm⟩
  · rintro ⟨k, first, rfl⟩
    exact observe_firstExit loop m input wf idx first

end Silmaril.SSA.PEG.Bridge.Theta.Proofs
