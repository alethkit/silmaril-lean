module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Views
public import Silmaril.SSA.PEG.Simple.While.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before vars inside all : List (Ty Data)}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params} {read : Reads m all}
variable {active : List (Fin all.length)}
variable {init : Tuple (Port before) vars} {body : Code P params (vars ++ before) inside}
variable {guard : Port inside .bool} {next : Tuple (Port inside) vars} {neg : P [.bool] .bool}
variable (view : View m env read active (.loop init body guard next neg))

private theorem atOuter {i fixed : Index all.length} {k : Nat}
    (h : Agrees (view.key :: active) (fixed.set view.key k) i) : Agrees active fixed i := by
  intro l member
  have eq := h l (List.mem_cons_of_mem _ member)
  rwa [Index.set, ite_eq_right (view.key_fresh member)] at eq

private theorem atKey {i fixed : Index all.length} {k : Nat}
    (h : Agrees (view.key :: active) (fixed.set view.key k) i) : i view.key = k := by
  have eq := h view.key (List.mem_cons_self)
  simpa [Index.set] using eq

theorem sampleAgrees {i fixed : Index all.length} (h : Agrees active fixed i) (k : Nat) :
    Agrees (view.key :: active) (fixed.set view.key k) (i.set view.key k) := by
  intro l member
  rcases List.mem_cons.mp member with rfl | outer
  · simp [Index.set]
  · simp only [Index.set, ite_eq_right (view.key_fresh outer), h l outer]

/-- The body sees the source store in its θ slots, uniformly at all indices
with the same enclosing coordinates and this loop's iteration. -/
@[expose] def AtIteration (fixed : Index all.length) (k : Nat) (store : Tuple m.Value vars) : Prop :=
  RealizesOn read (fun r => view.inner.embed (body.lift r))
    ((ports vars).map fun _ r => portLeft r) store (view.key :: active) (fixed.set view.key k)

private theorem slotAt {fixed j : Index all.length} {k : Nat} {store : Tuple m.Value vars}
    (h : AtIteration view fixed k store) (atJ : Agrees (view.key :: active) (fixed.set view.key k) j)
    {t : Ty Data} (slot : Port vars t) :
    read (view.inner.embed (body.lift (portLeft slot))) j = some (store.get slot) := by
  have eq := h j atJ _ slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get] at eq
  exact eq

private theorem thetaEquation {t : Ty Data} (slot : Port vars t) (j : Index all.length) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      rowValue m env
        ⟨_, .theta view.key,
          .cons (view.inner.embed (body.lift (portRight vars (init.get slot))))
            (.cons (view.inner.embed (next.get slot)) .nil), none⟩ read j := by
  have h := view.inner.eqs j t (body.lift (portLeft slot))
  change _ = rowValue m env
    (body.rows (loopHoles body init next view.holes view.embed) (fun r => view.inner.embed r)
      (some view.key) (body.lift (portLeft slot))) read j at h
  rw [rows_lift, loopHoles_left] at h
  exact h

private theorem thetaZero {t : Ty Data} (slot : Port vars t) (j : Index all.length)
    (zero : j view.key = 0) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      read (view.inner.embed (body.lift (portRight vars (init.get slot)))) j := by
  refine (thetaEquation view slot j).trans ?_
  simp only [rowValue, Label.interpret]
  generalize eq : j view.key = count at zero ⊢
  clear eq
  subst count
  rfl

private theorem thetaNext {t : Ty Data} (slot : Port vars t) (j : Index all.length) (k : Nat)
    (tick : j view.key = k + 1) :
    read (view.inner.embed (body.lift (portLeft slot))) j =
      read (view.inner.embed (next.get slot)) (j.set view.key k) := by
  refine (thetaEquation view slot j).trans ?_
  simp only [rowValue, Label.interpret]
  generalize eq : j view.key = count at tick ⊢
  clear eq
  subst count
  rfl

private theorem atEntry {fixed : Index all.length} {store : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init body guard next neg).lift r))
      init store active fixed) : AtIteration view fixed 0 store := by
  intro j atJ t slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact (thetaZero view slot j (atKey view atJ)).trans (entry j (atOuter view atJ) t slot)

private theorem stepIteration {fixed : Index all.length} {k : Nat} {store : Tuple m.Value vars}
    (h : RealizesOn read view.inner.embed next store (view.key :: active) (fixed.set view.key k)) :
    AtIteration view fixed (k + 1) store := by
  intro j atJ t slot
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact (thetaNext view slot j k (atKey view atJ)).trans
    (h _ (sampleAgrees view (atOuter view atJ) k) t slot)

private theorem collectOne (r : (i : Fin [Ty.bool].length) → Option (m.Value [Ty.bool][i])) :
    collect [.bool] r = (r 0).map (fun b => Tuple.cons b .nil) := by
  unfold collect
  cases r 0 <;> rfl

private theorem exitTest (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (j : Index all.length) {flag : Bool} (guardValue : read (view.inner.embed guard) j = some ⟨flag⟩) :
    read (view.embed (negRef vars)) j = some ⟨!flag⟩ := by
  refine (view.eqs j _ (negRef vars)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (negRef vars)) read j = _
  rw [loopRows_neg]
  change (collect (F := m.Value) [.bool] _).elim none (m.run neg) = _
  rw [collectOne]
  change ((read (view.inner.embed guard) j).map (fun x => .cons x .nil)).elim none (m.run neg) = _
  rw [guardValue]
  exact negSem flag

private structure Exits (fixed : Index all.length) (start count : Nat) (final : Tuple m.Value vars) : Prop where
  store : AtIteration view fixed (start + count) final
  stop : ∀ j, Agrees active fixed j →
    read (view.embed (negRef vars)) (j.set view.key (start + count)) = some ⟨true⟩
  prior : ∀ k < count, ∀ j, Agrees active fixed j →
    read (view.embed (negRef vars)) (j.set view.key (start + k)) = some ⟨false⟩
  defined : ∀ k < count, ∀ j, Agrees active fixed j → ∀ t (r : Port vars t),
    (read (view.inner.embed (body.lift (portLeft r))) (j.set view.key (start + k))).isSome

variable {test : Expr P vars .bool} {stmt : Stmt P true vars vars}

private theorem traceExit
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (fixed : Index all.length)
    (testCorrect : ∀ {k store} {b : Bool}, AtIteration view fixed k store →
      test.eval m store = some ⟨b⟩ → ∀ j, Agrees active fixed j →
      read (view.inner.embed guard) (j.set view.key k) = some ⟨b⟩)
    (bodyCorrect : ∀ {k store updated}, AtIteration view fixed k store →
      Exec m stmt store (some updated) →
      RealizesOn read view.inner.embed next updated (view.key :: active) (fixed.set view.key k))
    {count : Nat} {store final : Tuple m.Value vars}
    (trace : WhileTrace m test stmt count store final) (start : Nat)
    (entry : AtIteration view fixed start store) :
    Exits view fixed start count final := by
  induction trace generalizing start with
  | stop h =>
    refine ⟨entry, ?_, ?_, ?_⟩
    · intro j eq
      exact exitTest view negSem _ (testCorrect entry h j eq)
    · intro k lt
      omega
    · intro k lt
      omega
  | @step k store updated final h run tail ih =>
    have reached := ih (start + 1) (stepIteration view (bodyCorrect entry run))
    have offset (j : Nat) : start + (j + 1) = start + 1 + j := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [offset]
      exact reached.store
    · intro j eq
      rw [offset]
      exact reached.stop _ eq
    · intro i lt j eq
      cases i with
      | zero => exact exitTest view negSem _ (testCorrect entry h j eq)
      | succ i =>
        rw [offset]
        exact reached.prior i (by omega) j eq
    · intro i lt j eq t r
      cases i with
      | zero =>
        have atSlot := slotAt view entry (sampleAgrees view eq start) r
        change (read (view.inner.embed (body.lift (portLeft r))) (j.set view.key start)).isSome
        rw [atSlot]
        rfl
      | succ i =>
        rw [offset]
        exact reached.defined i (by omega) j eq t r

private theorem passValue {fixed : Index all.length} {k : Nat} {final : Tuple m.Value vars}
    (exit : Exits view fixed 0 k final) (j : Index all.length) (agree : Agrees active fixed j) :
    read (view.embed (passRef vars)) j = some ⟨k⟩ := by
  refine (view.eqs j _ (passRef vars)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (passRef vars)) read j = _
  rw [loopRows_pass]
  let flags := fun i => (read (view.embed (negRef vars)) (j.set view.key i)).map ULift.down
  change (firstTrue flags).map ULift.up = _
  have atExit : flags k = some true := by
    unfold flags
    have h := exit.stop j agree
    rw [Nat.zero_add] at h
    rw [h]
    rfl
  have before (i : Nat) (lt : i < k) : flags i = some false := by
    unfold flags
    have h := exit.prior i lt j agree
    rw [Nat.zero_add] at h
    rw [h]
    rfl
  have hit : firstTrue flags = some k := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨atExit, ?_⟩, ?_⟩
    · intro i lt
      rw [before i lt]
      rfl
    · intro i lt premature
      have value := ((monotonize_eq_some_iff _ _ _).mp premature).1
      rw [before i lt] at value
      contradiction
  rw [hit]
  rfl

private theorem evalValue {fixed : Index all.length} {k : Nat} {final : Tuple m.Value vars}
    (exit : Exits view fixed 0 k final) (j : Index all.length) (agree : Agrees active fixed j)
    {t : Ty Data} (r : Port vars t) :
    read (view.embed (portLeft r)) j = some (final.get r) := by
  refine (view.eqs j _ (portLeft r)).trans ?_
  change rowValue m env (loopRows body guard neg active.head? view.embed
    (body.rows view.inner.holes view.inner.embed (some view.key)) (portLeft r)) read j = _
  rw [loopRows_exit]
  change (read (view.embed (passRef vars)) j).elim none (fun count =>
    monotonize (fun i => read (view.inner.embed (body.lift (portLeft r))) (j.set view.key i)) count.down) = _
  rw [passValue view exit j agree]
  change monotonize (fun i => read (view.inner.embed (body.lift (portLeft r))) (j.set view.key i)) k = _
  apply (monotonize_eq_some_iff _ _ _).mpr
  constructor
  · have finalSample := slotAt view exit.store (sampleAgrees view agree (0 + k)) r
    simpa only [Nat.zero_add] using finalSample
  · intro i lt
    simpa only [Nat.zero_add] using exit.defined i lt j agree t r

theorem loopCorrect
    (negSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (fixed : Index all.length)
    (testCorrect : ∀ {k store} {b : Bool}, AtIteration view fixed k store →
      test.eval m store = some ⟨b⟩ → ∀ j, Agrees active fixed j →
      read (view.inner.embed guard) (j.set view.key k) = some ⟨b⟩)
    (bodyCorrect : ∀ {k store updated}, AtIteration view fixed k store →
      Exec m stmt store (some updated) →
      RealizesOn read view.inner.embed next updated (view.key :: active) (fixed.set view.key k))
    {store final : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => view.embed ((Code.loop init body guard next neg).lift r))
      init store active fixed)
    (run : Exec m (.while rfl test stmt) store (some final)) :
    RealizesOn read view.embed ((ports vars).map fun _ r => portLeft r) final active fixed := by
  obtain ⟨k, trace⟩ := run.while_trace
  have exit := traceExit view negSem fixed testCorrect bodyCorrect trace 0 (atEntry view entry)
  intro j agree t r
  rw [Simple.Proofs.get_map, Simple.Proofs.ports_get]
  exact evalValue view exit j agree r

end Silmaril.SSA.PEG.Simple.Structured.Proofs
