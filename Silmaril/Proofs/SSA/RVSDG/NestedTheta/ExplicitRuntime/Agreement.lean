module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Proofs

open OrderedRuntime Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {σ : Type (max u w)} {value : V → Type (max u w)}
variable {args ins out outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

set_option backward.isDefEq.respectTransparency false

private theorem boundary_decode (result : Tuple (Values value) outs × σ) :
    boundaryResult (decode result) = (withRuntime PUnit.unit result.1, result.2) := by
  rw [boundaryResult, erase_decode]
  exact congrArg (Prod.mk _) (get_runtime _ _)

private def boundaryEquiv (data : Data outs) :
    Tuple (RuntimeValues value σ) (Threaded outs) ≃ OrderedState.Configuration value σ (Threaded outs) where
  toFun := boundaryResult
  invFun result := decode ((splitRuntime outs result.1).1, result.2)
  left_inv input := by
    have h := decode_encode data input
    rw [← h]
    simp only [boundary_decode, split_append]
  right_inv result := by
    rw [boundary_decode]
    apply Prod.ext
    · exact append_split result.1
    · rfl

theorem boundary_bijective (data : Data outs) :
    Function.Bijective (boundaryResult (value := value) (σ := σ) (outs := outs)) :=
  (boundaryEquiv data).bijective

private theorem boundary_append (rt : σ) (xs : Tuple (RuntimeValues value σ) outs) :
    boundaryResult (withRuntime rt xs) = (withRuntime PUnit.unit (eraseTuple xs), rt) := by
  simp only [boundaryResult, erase_append, get_runtime]

private theorem boundary_tagged (m : Structured.Model P E (StateM σ)) (again : Bool)
    (x : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    boundaryResult (outs := Theta.BodyResults outs) (Theta.bodyResult m.toRVSDG again x) =
      OrderedState.tagged again (boundaryResult x) := rfl

private theorem iterate_map {X Y : Type w} (e : X ≃ Y)
    {p : X → Bool → X → Prop} {q : Y → Bool → Y → Prop}
    (step : ∀ x again y, p x again y ↔ q (e x) again (e y))
    {x y : X} : Theta.Iterate p x y ↔ Theta.Iterate q (e x) (e y) := by
  constructor
  · intro h
    induction h with
    | stop last => exact .stop ((step _ _ _).mp last)
    | again next _ ih => exact .again ((step _ _ _).mp next) ih
  · have backward {x y : Y} (h : Theta.Iterate q x y) :
        Theta.Iterate p (e.symm x) (e.symm y) := by
      have one {x y : Y} {again : Bool} (r : q x again y) : p (e.symm x) again (e.symm y) :=
        (step _ _ _).mpr (by simpa only [Equiv.apply_symm_apply] using r)
      induction h with
      | stop last => exact .stop (one last)
      | again next _ ih => exact .again (one next) ih
    intro h
    simpa only [Equiv.symm_apply_apply] using backward h

private theorem exists_map {X Y : Type w} (e : X ≃ Y) {p q : X → Prop} {r s : Y → Prop}
    (hp : ∀ x, p x ↔ r (e x)) (hq : ∀ x, q x ↔ s (e x)) :
    (∃ x, p x ∧ q x) ↔ ∃ y, r y ∧ s y := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨e x, (hp x).mp hx, (hq x).mp hy⟩
  · rintro ⟨y, hy, hz⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨x, (hp x).mpr hy, (hq x).mpr hz⟩

variable (m : Structured.Model P E (StateM σ))

private theorem primitive_mem (i : Data ins) (o : Data out) (op : Instruction P E ins out)
    (x : Tuple (RuntimeValues m.value σ) ins) (state : σ)
    (y : Tuple (RuntimeValues m.value σ) (Threaded out)) :
    m.toRVSDG.run (.ordered i o op) (withRuntime state x) = y ↔
      ((erasedModel m).step (eraseInstruction op) (withRuntime PUnit.unit (eraseTuple x))).run
        state = boundaryResult y := by
  let p := (m.step op (eraseTuple x)).run state
  have hl : m.toRVSDG.run (.ordered i o op) (withRuntime state x) = decode p := by
    simp only [Structured.Model.toRVSDG, split_append]
    rfl
  have hr : ((erasedModel m).step (eraseInstruction op) (withRuntime PUnit.unit (eraseTuple x))).run
       state = boundaryResult (decode p) := by
    rw [boundary_decode]
    cases op <;> simp [p, eraseInstruction, erasedModel, Structured.Model.step, split_append, StateT.run_map] <;> rfl
  rw [hl, hr]
  exact (boundaryEquiv o).injective.eq_iff.symm

private theorem next_boundary (o : Data out) (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (x : Tuple (RuntimeValues m.value σ) (Threaded out)) :
    readOrigin (nextRuntime past out) entry (locals.snoc x) = (boundaryResult x).2 := by
  rw [← decode_encode o x, next_decode, boundary_decode]

theorem exec_iff {a : Data args} {b : Data outs}
    {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t) :
    ∀ (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
      (locals : Locals (RuntimeValues m.value σ) past)
      (output : Tuple (RuntimeValues m.value σ) (Threaded outs)),
      t.Exec m.toRVSDG entry locals output ↔
        OrderedState.exec (erasedModel m) checked.erase (eraseTuple entry) (eraseLocals past locals)
          (readOrigin live entry locals) (boundaryResult output) := by
  induction checked with
  | @ret args outs a b past live wires =>
    intro entry locals output
    simp only [Term.Exec, Checked.erase, OrderedState.exec, erase_read, read_appended]
    rw [erase_append, ← boundary_append]
    exact (boundaryEquiv b).injective.eq_iff.symm
  | @primitive args outs ins out a b past sigs live i o op wires rest checked ih =>
    intro entry locals output
    simp only [Term.Exec, Checked.erase, OrderedState.exec]
    apply exists_map (boundaryEquiv o)
    · intro x
      simp only [Kind.Exec, OrderedState.kindExec, Structured.primitiveNode,
        read_appended, erase_read, erase_append]
      exact primitive_mem m i o op _ _ x
    · intro x
      change _ ↔ OrderedState.exec (erasedModel m) checked.erase (eraseTuple entry)
        ((eraseLocals past locals).snoc (eraseTuple x)) (boundaryResult x).2 (boundaryResult output)
      rw [← erase_snoc, ← next_boundary m o]
      exact ih entry (locals.snoc x) output
  | @gamma args outs ins out a b past sigs extra choice live i o wires childSigs children rest arms checked ihArms ih =>
    intro entry locals output
    simp only [Term.Exec, Checked.erase, OrderedState.exec]
    apply exists_map (boundaryEquiv o)
    · intro x
      simp only [read_cons, read_appended, erase_read, Kind.Exec, OrderedState.kindExec]
      let tag := (readOrigin choice entry locals).down
      let input := withRuntime (readOrigin live entry locals) (wires.read entry locals)
      change (children tag).Exec m.toRVSDG input PUnit.unit x ↔
        OrderedState.exec (erasedModel m) (arms tag).erase (eraseTuple input) PUnit.unit
          (readOrigin live entry locals) (boundaryResult x)
      have sim := ihArms tag input PUnit.unit x
      change _ ↔ OrderedState.exec (erasedModel m) (arms tag).erase (eraseTuple input) PUnit.unit
        (input.get (runtimePort ins)) (boundaryResult x) at sim
      simpa only [input, get_runtime] using sim
    · intro x
      change _ ↔ OrderedState.exec (erasedModel m) checked.erase (eraseTuple entry)
        ((eraseLocals past locals).snoc (eraseTuple x)) (boundaryResult x).2 (boundaryResult output)
      rw [← erase_snoc, ← next_boundary m o]
      exact ih entry (locals.snoc x) output
  | @theta args outs ins a b past sigs live i wires bodySigs children rest admitted checked ihBody ih =>
    intro entry locals output
    simp only [Term.Exec, Checked.erase, OrderedState.exec]
    apply exists_map (boundaryEquiv i)
    · intro x
      simp only [read_appended, erase_read, erase_append, Kind.Exec, OrderedState.kindExec]
      have one (before after : Tuple (RuntimeValues m.value σ) (Threaded ins)) (again : Bool) :
          (children (0 : Fin 1)).Exec m.toRVSDG before PUnit.unit (Theta.bodyResult m.toRVSDG again after) ↔
            OrderedState.exec (erasedModel m) (admitted (0 : Fin 1)).erase
              (boundaryResult before).1 PUnit.unit (boundaryResult before).2
              (OrderedState.tagged again (boundaryResult after)) := by
        rw [← boundary_tagged m]
        exact ihBody (0 : Fin 1) before PUnit.unit _
      have loop := iterate_map (boundaryEquiv i)
        (p := fun before again after =>
          (children (0 : Fin 1)).Exec m.toRVSDG before PUnit.unit (Theta.bodyResult m.toRVSDG again after))
        (q := fun before again after => OrderedState.exec (erasedModel m) (admitted (0 : Fin 1)).erase
          before.1 PUnit.unit before.2 (OrderedState.tagged again after))
        (fun before again after => one before after again)
        (x := withRuntime (readOrigin live entry locals) (wires.read entry locals)) (y := x)
      change _ ↔ Theta.Iterate _ (boundaryResult (withRuntime (readOrigin live entry locals)
        (wires.read entry locals))) (boundaryResult x) at loop
      rw [boundary_append] at loop
      exact loop
    · intro x
      change _ ↔ OrderedState.exec (erasedModel m) checked.erase (eraseTuple entry)
        ((eraseLocals past locals).snoc (eraseTuple x)) (boundaryResult x).2 (boundaryResult output)
      rw [← erase_snoc, ← next_boundary m i]
      exact ih entry (locals.snoc x) output

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Proofs
