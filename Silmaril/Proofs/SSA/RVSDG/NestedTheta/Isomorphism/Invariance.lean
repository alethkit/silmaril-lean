module

public import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Isomorphism.Trace

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Proofs

open RVSDG.Isomorphism.Proofs (colours colours_injective source_before site_length extend_length)

universe u v w

variable {Ty : Type u} {F : Ty → Type w}

private theorem option_colours_injective {ts : Ports Ty} {left right : Option (Tuple F ts)}
    (eq : left.map colours = right.map colours) : left = right := by
  cases left <;> cases right
  · rfl
  · cases eq
  · cases eq
  · exact congrArg some (colours_injective _ _ (Option.some.inj eq))

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}

private theorem compare_label (m : Model.{u, v, w} Op) (fuel : Nat) {left right : NodeLabel Op}
    (same : left = right)
    (runLeft : Fin left.arity → Tuple m.Val left.kind.entry → Option (Tuple m.Val left.kind.exit))
    (runRight : Fin right.arity → Tuple m.Val right.kind.entry → Option (Tuple m.Val right.kind.exit))
    (input : Option (Tuple m.Val left.ins)) (input' : Option (Tuple m.Val right.ins))
    (equalInputs : input.map colours = input'.map colours)
    (children : ∀ arm arg arg', colours arg = colours arg' →
      (runLeft arm arg).map colours =
        (runRight (Fin.cast (congrArg NodeLabel.arity same) arm) arg').map colours) :
    (input >>= left.kind.eval m fuel runLeft).map colours =
      (input' >>= right.kind.eval m fuel runRight).map colours := by
  subst right
  have equal := option_colours_injective equalInputs
  subst input'
  obtain ⟨ins, outs, kind⟩ := left
  have runners : runLeft = runRight := by
    funext arm entry
    exact option_colours_injective (children arm entry entry rfl)
  rw [runners]

private theorem compare_completed {n k : Nat} (ids : Fin n ≃ Fin k) (left right : Erased F)
    (lenL : left.length = n) (lenR : right.length = k)
    (vertices : ∀ i, i < n → left[i]? = right[renameVertex ids i]?) :
    completed left = completed right := by
  apply propext
  simp only [completed, List.all_eq_true]
  constructor
  · intro done item mem
    obtain ⟨j, hj, atJ⟩ := List.mem_iff_getElem.mp mem
    let target : Fin k := ⟨j, lenR ▸ hj⟩
    let source := ids.symm target
    have same := vertices source.val source.isLt
    have atR : right[renameVertex ids source.val]? = some item := by
      have address : renameVertex ids source.val = j := by
        change renameVertex ids source.val = target.val
        simp only [renameVertex, dite_eq_left source.isLt]
        exact congrArg Fin.val (ids.apply_symm_apply target)
      rw [address, List.getElem?_eq_getElem hj, atJ]
    exact done item (List.mem_of_getElem? (same.trans atR))
  · intro done item mem
    obtain ⟨i, hi, atI⟩ := List.mem_iff_getElem.mp mem
    have same := vertices i (lenL ▸ hi)
    rw [List.getElem?_eq_getElem hi, atI] at same
    exact done item (List.mem_of_getElem? same.symm)

private theorem run_colours {argsL argsR outsL outsR : Ports (PortType V S)}
    {sigsL sigsR : List (Ports (PortType V S))}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op) (fuel : Nat)
    (inputL : Tuple m.Val argsL) (inputR : Tuple m.Val argsR)
    (inputEq : colours inputL = colours inputR) :
    (left.run m fuel inputL).map colours = (right.run m fuel inputR).map colours := by
  classical
  induction iso with
  | @intro argsL argsR outsL outsR sigsL sigsR left right _ _ ids labels inputs results _ childIH =>
    let allL := store (graphTrace m fuel left inputL)
    let allR := store (graphTrace m fuel right inputR)
    have vertices (n : Nat) (valid : n < sigsL.length) :
        allL[n]? = allR[renameVertex ids n]? := by
      induction n using Nat.strongRecOn with
      | ind n earlier =>
        let i : Fin sigsL.length := ⟨n, valid⟩
        obtain ⟨beforeL, prefL, atL⟩ := graphTrace_at m fuel left inputL i
        obtain ⟨beforeR, prefR, atR⟩ := graphTrace_at m fuel right inputR (ids i)
        simp only [renameVertex, dite_eq_left valid]
        change allL[i.val]? = allR[(ids i).val]?
        rw [atL, atR]
        apply congrArg some
        refine compare_label m fuel (labels i) _ _ _ _ ?_ (childIH i)
        apply compare_reads _ _ inputL inputR inputEq beforeL beforeR prefL prefR _ (inputs i)
        intro producer port mem
        have earlierProducer : producer < n := by
          simpa only [site_length, List.length_nil, Nat.zero_add, i] using
            source_before (left.nodes i).inputs mem
        exact earlier producer earlierProducer (Nat.lt_trans earlierProducer valid)
    have lenL : allL.length = sigsL.length := by simp [allL, store_length, extend_length]
    have lenR : allR.length = sigsR.length := by simp [allR, store_length, extend_length]
    have done := compare_completed ids allL allR lenL lenR vertices
    rw [graphTrace_result, graphTrace_result]
    change (if completed allL then _ else none).map colours =
      (if completed allR then _ else none).map colours
    by_cases status : completed allR
    · have statusL : completed allL := Eq.mpr done status
      simp only [ite_eq_left statusL, ite_eq_left status]
      refine compare_reads left.results right.results inputL inputR inputEq _ _
        ⟨[], List.append_nil _⟩ ⟨[], List.append_nil _⟩ _ results ?_
      intro producer port mem
      apply vertices
      simpa only [extend_length, List.length_nil, Nat.zero_add] using source_before left.results mem
    · have statusL : ¬ completed allL := fun h => status (Eq.mp done h)
      simp only [ite_eq_right statusL, ite_eq_right status, Option.map_none]

theorem run_eq {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op) (fuel : Nat)
    (entry : Tuple m.Val args) : left.run m fuel entry = right.run m fuel entry :=
  option_colours_injective (run_colours iso m fuel entry entry rfl)

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Proofs
