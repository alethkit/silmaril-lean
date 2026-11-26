module

public import Silmaril.Proofs.SSA.PEG.Simple.While.Rows
public import Silmaril.Proofs.SSA.PEG.Simple.While.Trace

public section

namespace Silmaril.SSA.PEG.Simple.WhileProofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {out : Ty Data}
variable (p : WhileProgram P params out) (neg : P [.bool] .bool)
variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

private def clock (k : Nat) : Index 1 := fun _ => k

private theorem setClock (i : Index 1) (k : Nat) : i.set 0 k = clock k := by
  funext j
  have same : j = 0 := Fin.ext (by have := j.isLt; omega)
  subst j
  rfl

private def thetaRef {t : Ty Data} (slot : Port params t) : Port p.layout t :=
  p.localRef (p.core.code.lift slot)

private def guardRef : Port p.layout .bool := p.localRef (p.core.refs.get .head)

private def exitRef : Port p.layout .bool := .tail (.tail .head)

private def passRef : Port p.layout .count := .tail .head

variable (read : ∀ {t}, Port p.layout t → Index 1 → Option (m.Value t))

private def Carries (k : Nat) (store : Tuple m.Value params) : Prop :=
  ∀ t (slot : Port params t), read (thetaRef p slot) (clock k) = some (store.get slot)

variable (eqs : ∀ (i : Index 1) t (r : Port p.layout t),
  read r i = rowValue m env (p.row neg r) read i)

include eqs

private theorem thetaEq {t : Ty Data} (slot : Port params t) (k : Nat) :
    read (thetaRef p slot) (clock k) = rowValue m env (p.thetaRow slot) read (clock k) := by
  rw [eqs]
  unfold thetaRef
  rw [localRow, liftedRow]

private theorem atEntry : Carries p m read 0 env := by
  intro t slot
  refine (thetaEq p neg m env read eqs slot 0).trans ?_
  change read (p.paramRef slot) (clock 0) = _
  rw [eqs, paramRow]
  rfl

private theorem thetaNext {t : Ty Data} (slot : Port params t) (k : Nat) :
    read (thetaRef p slot) (clock (k + 1)) =
      read (p.localRef (p.core.refs.get (.tail slot))) (clock k) := by
  refine (thetaEq p neg m env read eqs slot (k + 1)).trans ?_
  change read (p.localRef (p.core.refs.get (.tail slot))) ((clock (k + 1)).set 0 k) = _
  rw [setClock]

private theorem evalCore {k : Nat} {store : Tuple m.Value params}
    (entry : Carries p m read k store) (t : Ty Data) (slot : Port p.core.nodes t) :
    read (p.localRef slot) (clock k) =
      (p.core.code.eval m env (store.map fun _ v => some v)).get slot := by
  apply closedEval m env p.core.code (p.thetaRow ·) (p.localRef ·) read (clock k)
  · intro t r
    rw [Proofs.get_map]
    exact entry t r
  · intro t r
    rw [eqs, localRow]

omit eqs in
private theorem seedRealizes (store : Tuple m.Value params) :
    Realizes m (store.map fun _ v => some v) (ports params) store := by
  intro t slot
  rw [Proofs.ports_get, Proofs.get_map]

private theorem guardAt {k : Nat} {store : Tuple m.Value params}
    (entry : Carries p m read k store) {b : Bool} (test : p.guard.eval m store = some ⟨b⟩) :
    read (guardRef p) (clock k) = some ⟨b⟩ := by
  unfold guardRef
  rw [evalCore p neg m env read eqs entry]
  let c := p.guard.lower (params := params) (ports params)
  let a := p.body.lower (params := params) (c.code.liftRefs (ports params))
  let seed := store.map fun _ v => some v
  change ((c.code.append a.code).eval m env seed).get (a.code.lift (c.refs.get .head)) = _
  rw [Proofs.eval_append, Proofs.eval_lift]
  exact Proofs.expr_correct m env p.guard (ports params) seed store (seedRealizes m store) test

private theorem bodyAt {k : Nat} {store next : Tuple m.Value params}
    (entry : Carries p m read k store) (run : Exec m p.body.enableWhile store (some next)) :
    Carries p m read (k + 1) next := by
  intro t slot
  change read (thetaRef p slot) (clock (k + 1)) = _
  rw [thetaNext p neg m env read eqs, evalCore p neg m env read eqs entry]
  let c := p.guard.lower (params := params) (ports params)
  let a := p.body.lower (params := params) (c.code.liftRefs (ports params))
  let seed := store.map fun _ v => some v
  change ((c.code.append a.code).eval m env seed).get (a.refs.get slot) = _
  rw [Proofs.eval_append]
  have entryBody := Proofs.realizes_lift m env c.code (seedRealizes m store)
  exact Proofs.stmt_correct m env p.body (c.code.liftRefs (ports params)) _
    entryBody (forgetEnabled p.body run) t slot

omit eqs in
private theorem collectOne (collectRead : (j : Fin [Ty.bool].length) → Option (m.Value [Ty.bool][j])) :
    collect [.bool] collectRead = (collectRead 0).map (fun x => Tuple.cons x .nil) := by
  unfold collect
  cases collectRead 0 <;> rfl

private theorem exitAt
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {store : Tuple m.Value params} (entry : Carries p m read k store)
    {b : Bool} (test : p.guard.eval m store = some ⟨b⟩) :
    read (exitRef p) (clock k) = some ⟨!b⟩ := by
  rw [eqs]
  change (collect (F := m.Value) [.bool] _).elim none (m.run neg) = _
  rw [collectOne]
  change ((read (guardRef p) (clock k)).map (fun x => .cons x .nil)).elim none (m.run neg) = _
  rw [guardAt p neg m env read eqs entry test]
  exact notSem b

private structure Reaches (i k : Nat) (final : Tuple m.Value params) : Prop where
  carries : Carries p m read (i + k) final
  exit : read (exitRef p) (clock (i + k)) = some ⟨true⟩
  earlier : ∀ j < k, read (exitRef p) (clock (i + j)) = some ⟨false⟩
  defined : ∀ j < k, ∀ t (slot : Port params t),
    (read (thetaRef p slot) (clock (i + j))).isSome

private theorem traceCorrect
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {k : Nat} {store final : Tuple m.Value params}
    (run : WhileTrace m p.guard p.body.enableWhile k store final)
    (i : Nat) (entry : Carries p m read i store) : Reaches p m read i k final := by
  induction run generalizing i with
  | stop test =>
    refine ⟨entry, exitAt p neg m env read eqs notSem entry test, ?_, ?_⟩
    · intro j lt
      omega
    · intro j lt
      omega
  | @step k store next final test step rest ih =>
    have next := bodyAt p neg m env read eqs entry step
    have reached := ih (i + 1) next
    have offset (j : Nat) : i + (j + 1) = i + 1 + j := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [offset]
      exact reached.carries
    · rw [offset]
      exact reached.exit
    · intro j lt
      cases j with
      | zero => exact exitAt p neg m env read eqs notSem entry test
      | succ j =>
        rw [offset]
        exact reached.earlier j (by omega)
    · intro j lt t slot
      cases j with
      | zero =>
        have sample := entry t slot
        change read (thetaRef p slot) (clock i) = _ at sample
        rw [Nat.add_zero, sample]
        rfl
      | succ j =>
        rw [offset]
        exact reached.defined j (by omega) t slot

private theorem passAt {k : Nat} {final : Tuple m.Value params}
    (reached : Reaches p m read 0 k final) (i : Index 1) :
    read (passRef p) i = some ⟨k⟩ := by
  rw [eqs]
  change (firstTrue (fun j => (read (exitRef p) (i.set 0 j)).map ULift.down)).map ULift.up = _
  have stream (j : Nat) : (read (exitRef p) (i.set 0 j)).map ULift.down =
      (read (exitRef p) (clock j)).map ULift.down := by rw [setClock]
  simp only [stream]
  let flags := fun j => (read (exitRef p) (clock j)).map ULift.down
  have atExit : flags k = some true := by
    have sample := reached.exit
    change read (exitRef p) (clock (0 + k)) = _ at sample
    rw [Nat.zero_add] at sample
    unfold flags
    rw [sample]
    rfl
  have before (j : Nat) (lt : j < k) : flags j = some false := by
    have sample := reached.earlier j lt
    change read (exitRef p) (clock (0 + j)) = _ at sample
    rw [Nat.zero_add] at sample
    unfold flags
    rw [sample]
    rfl
  have first : firstTrue flags = some k := by
    apply (firstTrue_eq_some_iff _ _).mpr
    refine ⟨(monotonize_eq_some_iff _ _ _).mpr ⟨atExit, ?_⟩, ?_⟩
    · intro j lt
      rw [before j lt]
      rfl
    · intro j lt hit
      have pick := ((monotonize_eq_some_iff _ _ _).mp hit).1
      rw [before j lt] at pick
      contradiction
  change (firstTrue flags).map ULift.up = _
  rw [first]
  rfl

private theorem evalAt {k : Nat} {final : Tuple m.Value params}
    (reached : Reaches p m read 0 k final) (i : Index 1) :
    read (Port.head : Port p.layout out) i = some (final.get p.retvar) := by
  rw [eqs]
  change (read (passRef p) i).elim none (fun count =>
    monotonize (fun j => read (thetaRef p p.retvar) (i.set 0 j)) count.down) = _
  rw [passAt p neg m env read eqs reached i]
  change monotonize (fun j => read (thetaRef p p.retvar) (i.set 0 j)) k = _
  apply (monotonize_eq_some_iff _ _ _).mpr
  constructor
  · rw [setClock]
    simpa only [Nat.zero_add] using reached.carries _ p.retvar
  · intro j lt
    rw [setClock]
    simpa only [Nat.zero_add] using reached.defined j lt _ p.retvar

omit eqs in
theorem returns
    (notSem : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value out} (run : p.source.Returns m env value)
    {values : (p.translate neg).Valuation m} (solves : (p.translate neg).Solves m env values)
    (i : Index 1) :
    (p.translate neg).observe m values i = .cons (some value) .nil := by
  obtain ⟨final, exec, returnValue⟩ := run
  obtain ⟨k, trace⟩ := whileTrace exec
  let read := fun {t} (slot : Port p.layout t) => readPort m p neg values slot
  have eqs := fun i t slot => equationAt m env p neg solves i t slot
  have reached := traceCorrect p neg m env read eqs notSem trace 0 (atEntry p neg m env read eqs)
  have output := evalAt p neg m env read eqs reached i
  change Tuple.cons (F := fun t => Option (m.Value t)) (read Port.head i) .nil = _
  rw [output]
  change final.get p.retvar = value at returnValue
  rw [returnValue]

end Silmaril.SSA.PEG.Simple.WhileProofs
