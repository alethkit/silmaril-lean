module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
public import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Rows

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Proofs

open RVSDG (Port Tuple)
open Region.Proofs (clock setClock)

set_option backward.isDefEq.respectTransparency false

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried results vars ins : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P [] results n 1} {m : Interpretation.{u,v,w} P}
variable {values : g.Valuation m}

private abbrev read (values : g.Valuation m) (idx : Index 1) (ref : Ref g.sort t) :=
  Rules.readRef values ref idx

private theorem tuple_ext {F : Ty Data → Type w} (a b : Tuple F vars)
    (get : ∀ s (p : Port vars s), a.get p = b.get p) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys => exact congrArg₂ Tuple.cons (get _ .head) (ih ys fun s p => get s (.tail p))

private theorem hasNode {r : Ref g.sort t} {label : Label P [] (Fin 1) ins t}
    {args : Tuple (Ref g.sort) ins} (eq : nodeAt g r = .ofLabel label args) :
    Rules.HasNode r label args := by
  obtain ⟨i, typed⟩ := r
  cases typed
  exact heq_of_eq eq

variable (a : Accepted g carried)

private abbrev Tagged := Tuple m.Value (.bool :: carried)

private def old (store : Tagged (m := m) (carried := carried)) : Tuple m.Value carried :=
  match store with | .cons _ xs => xs

private theorem old_eq (store : Tagged (m := m) (carried := carried)) :
    ((oldSlots carried).map fun _ p => store.get p) = old store := by
  apply tuple_ext
  intro s p
  rw [get_map, oldSlots, get_map, ports_get]
  cases store
  rfl

private abbrev At (values : g.Valuation m) (k : Nat) (store : Tagged (m := m) (carried := carried)) :=
  Region.Proofs.Realizes (g := a.descriptor.view) values (clock k) a.descriptor.tagged store ∧
    store.get (.tail a.descriptor.clock) = ⟨k⟩

private theorem initial (laws : a.Laws m) (solves : g.Solves m .nil values)
    {start : Tagged (m := m) (carried := carried)}
    (ran : a.startCode.runLoopFree m .nil = some start) : At a values 0 start := by
  obtain ⟨initial, ranInit, guard⟩ := Option.bind_eq_some_iff.mp ran
  have base := Region.Proofs.schedule a.start solves
    (fun _ p => nomatch p) ranInit (idx := clock 0)
  have theta (s : Ty Data) (p : Port carried s) :
      read (g := g) values (clock 0) (a.descriptor.theta.get p) = some (initial.get p) :=
    (Rules.theta_zero solves (hasNode (a.boundary.theta s p)) rfl).trans (base s p)
  have zero := Region.Proofs.row (g := a.descriptor.view) solves (clock 0)
    (a.descriptor.initial.get a.descriptor.clock)
  change read (g := g) values (clock 0) (a.descriptor.initial.get a.descriptor.clock) =
    (let node := nodeAt g (a.descriptor.initial.get a.descriptor.clock)
     node.label.interpret m .nil (clock 0) fun slot j _ => read (g := g) values j (node.arg slot)) at zero
  rw [a.boundary.zero] at zero
  change _ = m.run a.descriptor.zero .nil at zero
  have tagged := Region.Proofs.schedule a.guard solves theta guard
  have startClock : read (g := g) values (clock 0) (a.descriptor.theta.get a.descriptor.clock) =
      some (start.get (.tail a.descriptor.clock)) := tagged .count (.tail a.descriptor.clock)
  exact ⟨tagged, Option.some.inj
    (startClock.symm.trans ((Rules.theta_zero solves (hasNode (a.boundary.theta _ _)) rfl).trans
      (zero.trans laws.zero)))⟩

private theorem advance (laws : a.Laws m) (solves : g.Solves m .nil values)
    {k : Nat} {store final : Tagged (m := m) (carried := carried)} (current : At a values k store)
    (step : Exec m a.body.enableWhile store (some final)) : At a values (k + 1) final := by
  have ran := Exec.deterministic (a.body.runLoopFree_enableWhile store) step
  change ((some ((oldSlots carried).map fun _ p => store.get p)).bind fun old =>
    (a.step.lower.runLoopFree m old).bind (a.guard.lower.runLoopFree m)) = some final at ran
  rw [old_eq, Option.bind_some] at ran
  obtain ⟨next, ranStep, ranGuard⟩ := Option.bind_eq_some_iff.mp ran
  have before : Region.Proofs.Realizes (g := a.descriptor.view) values (clock k)
      a.descriptor.theta (old store) := by
    cases store with | cons flag xs => exact fun s p => current.1 s (.tail p)
  have update := Region.Proofs.schedule a.step solves before ranStep
  have theta (s : Ty Data) (p : Port carried s) :
      read (g := g) values (clock (k + 1)) (a.descriptor.theta.get p) = some (next.get p) := by
    rw [read, Rules.theta_succ solves (hasNode (a.boundary.theta s p)) (i := clock (k + 1))
      (k := k) rfl, setClock]
    exact update s p
  have clockBefore : read (g := g) values (clock k) (a.descriptor.theta.get a.descriptor.clock) =
      some ⟨k⟩ := (current.1 .count (.tail a.descriptor.clock)).trans (congrArg some current.2)
  have tick := Rules.unary_at solves (hasNode a.boundary.tick) (clock k)
  change read (g := g) values (clock k) (a.descriptor.next.get a.descriptor.clock) =
    (read (g := g) values (clock k) (a.descriptor.theta.get a.descriptor.clock)).bind _ at tick
  rw [clockBefore, Option.bind_some, laws.tick] at tick
  have tagged := Region.Proofs.schedule a.guard solves theta ranGuard
  have finalClock : read (g := g) values (clock (k + 1)) (a.descriptor.theta.get a.descriptor.clock) =
      some (final.get (.tail a.descriptor.clock)) := tagged .count (.tail a.descriptor.clock)
  refine ⟨tagged, Option.some.inj (finalClock.symm.trans ?_)⟩
  rw [read, Rules.theta_succ solves (hasNode (a.boundary.theta _ _)) (i := clock (k + 1))
    (k := k) rfl, setClock]
  exact tick

private def flags (values : g.Valuation m) (k : Nat) : Option Bool :=
  (read (g := g) values (clock k) a.descriptor.exit).map ULift.down

private theorem flag (laws : a.Laws m) {k : Nat} {store : Tagged (m := m) (carried := carried)}
    (atStore : At a values k store) {b : Bool}
    (test : a.test.eval m store = some ⟨b⟩) : flags a values k = some (!b) := by
  have existsFlag := atStore.1 .bool (.head)
  change read (g := g) values (clock k) a.descriptor.exit = some (store.get .head) at existsFlag
  unfold flags
  rw [existsFlag]
  have testEq : m.run a.descriptor.negate (.cons (store.get .head) .nil) = some ⟨b⟩ := test
  have inv := laws.negate (store.get .head).down
  have eq : (!(store.get .head).down) = b := congrArg ULift.down (Option.some.inj (inv.symm.trans testEq))
  rw [← eq]
  simp

private structure Prefix (values : g.Valuation m) (offset k : Nat)
    (final : Tagged (m := m) (carried := carried)) : Prop where
  finalAt : At a values (offset + k) final
  stop : flags a values (offset + k) = some true
  before : ∀ j < k, flags a values (offset + j) = some false
  defined : ∀ j < k, ∀ s (p : Port carried s),
    (read (g := g) values (clock (offset + j)) (a.descriptor.theta.get p)).isSome

private theorem trace_prefix (laws : a.Laws m) (solves : g.Solves m .nil values)
    {start final : Tagged (m := m) (carried := carried)} {k : Nat}
    (trace : WhileTrace m a.test a.body.enableWhile k start final)
    (i : Nat) (entry : At a values i start) : Prefix a values i k final := by
  induction trace generalizing i with
  | stop test =>
    exact ⟨entry, flag a laws entry test, fun j lt => (Nat.not_lt_zero j lt).elim,
      fun j lt => (Nat.not_lt_zero j lt).elim⟩
  | @step k start next final test step rest ih =>
    have tail := ih (i + 1) (advance a laws solves entry step)
    have same (j : Nat) : i + (j + 1) = i + 1 + j := by omega
    refine ⟨by rw [same]; exact tail.finalAt, by rw [same]; exact tail.stop, ?_, ?_⟩
    · intro j lt
      cases j with
      | zero => exact flag a laws entry test
      | succ j => rw [same]; exact tail.before j (by omega)
    · intro j lt s p
      cases j with
      | zero =>
        have defined := entry.1 s (.tail p)
        change read (g := g) values (clock i) (a.descriptor.theta.get p) = _ at defined
        rw [Nat.add_zero, defined]
        rfl
      | succ j => rw [same]; exact tail.defined j (by omega) s p

private theorem pass_read (solves : g.Solves m .nil values) (idx : Index 1) :
    read (g := g) values idx a.descriptor.pass = (firstTrue (flags a values)).map ULift.up := by
  rw [read, Rules.pass_at solves (hasNode a.boundary.pass) idx]
  unfold flags
  simp only [setClock]

private theorem readout (solves : g.Solves m .nil values) (idx : Index 1) {k : Nat}
    {final : Tagged (m := m) (carried := carried)} (facts : Prefix a values 0 k final)
    (pass : read (g := g) values idx a.descriptor.pass = some ⟨k⟩)
    (root : Ref g.sort t) (out : Readout carried t) (wired : a.descriptor.rootRow root out) :
    read (g := g) values idx root = some (final.get (a.descriptor.slot out)) := by
  cases out with
  | pass =>
    change root = a.descriptor.pass at wired
    have count := facts.finalAt.2
    rw [Nat.zero_add] at count
    change read (g := g) values idx root = some (final.get (.tail a.descriptor.clock))
    rw [wired, pass, count]
  | eval port =>
    change Rules.readRef values a.descriptor.pass idx = some ⟨k⟩ at pass
    rw [read, Rules.eval_at solves (hasNode wired) idx, pass]
    change monotonize (fun j =>
      read (g := g) values (idx.set 0 j) (a.descriptor.theta.get port)) k =
        some (final.get (.tail port))
    simp only [setClock]
    apply (monotonize_eq_some_iff _ _ _).mpr
    have last : read (g := g) values (clock (0 + k)) (a.descriptor.theta.get port) =
        some (final.get (.tail port)) := facts.finalAt.1 _ (.tail port)
    exact ⟨by simpa only [Nat.zero_add] using last,
      fun j hj => by simpa only [Nat.zero_add] using facts.defined j hj _ port⟩

theorem observe_of_exec (laws : a.Laws m) (solves : g.Solves m .nil values) (idx : Index 1)
    {output : Tuple m.Value results} (ran : Exec m a.revert .nil (some output)) :
    g.observe m values idx = output.map (fun _ => some) := by
  change Exec m (.seq a.startCode.enableWhile
    (.seq (.while rfl a.test a.body.enableWhile) (.project a.descriptor.slots))) .nil (some output) at ran
  cases ran with
  | seq start rest =>
    cases rest with
    | seq loop project =>
      obtain ⟨k, trace⟩ := Exec.while_trace loop
      have facts := trace_prefix a laws solves trace 0
        (initial a laws solves (Exec.deterministic (a.startCode.runLoopFree_enableWhile .nil) start))
      have first : firstTrue (flags a values) = some k :=
        (firstTrue_eq_some_iff_samples _ _).mpr ⟨by simpa only [Nat.zero_add] using facts.stop,
          fun j hj => by simpa only [Nat.zero_add] using facts.before j hj⟩
      have pass : read (g := g) values idx a.descriptor.pass = some ⟨k⟩ := by
        rw [pass_read a solves, first]
        rfl
      cases project with
      | project =>
        apply tuple_ext
        intro s port
        rw [Graph.observe, get_map, get_map, get_map, Descriptor.slots, get_map]
        exact readout a solves idx facts pass _ _ (a.boundary.outputs s port)

theorem exec_of_runFuel (fuel : Nat) {output : Tuple m.Value results}
    (ran : a.runFuel m fuel = some output) : Exec m a.revert .nil (some output) := by
  have loop {fuel : Nat} {start : Tagged (m := m) (carried := carried)}
      (ran : a.runFrom m fuel start = some output) :
      Exec m (.seq (.while rfl a.test a.body.enableWhile) (.project a.descriptor.slots))
        start (some output) := by
    suffices ∃ final, Exec m (.while rfl a.test a.body.enableWhile) start (some final) ∧
        (a.descriptor.slots.map fun _ p => final.get p) = output by
      obtain ⟨final, ranLoop, projected⟩ := this
      exact .seq ranLoop (projected ▸ .project)
    induction fuel generalizing start with
    | zero =>
      rw [Accepted.runFrom] at ran
      cases flag : a.test.eval m start with
      | none => simp [flag] at ran
      | some value =>
        obtain ⟨b⟩ := value
        cases b
        · exact ⟨start, .whileStop flag, Option.some.inj (by simpa [flag] using ran)⟩
        · simp [flag] at ran
    | succ k ih =>
      rw [Accepted.runFrom] at ran
      cases flag : a.test.eval m start with
      | none => simp [flag] at ran
      | some value =>
        obtain ⟨b⟩ := value
        cases b
        · exact ⟨start, .whileStop flag, Option.some.inj (by simpa [flag] using ran)⟩
        · rw [flag] at ran
          change (a.body.runLoopFree m start).bind (a.runFrom m k) = some output at ran
          obtain ⟨next, step, remaining⟩ := Option.bind_eq_some_iff.mp ran
          obtain ⟨final, trace, returned⟩ := ih remaining
          exact ⟨final, .whileStep flag (step ▸ a.body.runLoopFree_enableWhile start) trace, returned⟩
  obtain ⟨start, initialized, remaining⟩ := Option.bind_eq_some_iff.mp ran
  exact .seq (initialized ▸ a.startCode.runLoopFree_enableWhile .nil) (loop remaining)

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Proofs
