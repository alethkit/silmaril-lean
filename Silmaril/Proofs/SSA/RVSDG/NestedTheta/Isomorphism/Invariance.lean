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
variable {G : PortType V S → Type w}
variable {args outs : Ports (PortType V S)} {sigs sigs' : List (Ports (PortType V S))}

private theorem rename_refl (n : Nat) (address : Address) :
    address.rename (renameVertex (Equiv.refl (Fin n))) = address := by
  cases address with
  | arg => rfl
  | output vertex port => by_cases bounded : vertex < n <;> simp [Address.rename, renameVertex, bounded]

theorem refl {past : List (Ports (PortType V S))} (g : Graph Op args past sigs outs) (closed : past = []) :
    Graph.Isomorphic Op (closed ▸ g) (closed ▸ g) := by
  induction g with
  | region nodes children results ih =>
    subst_vars
    refine .intro rfl rfl (Equiv.refl _) (fun _ => rfl) (fun _ => ?_) ?_ (fun i j => ih i j rfl)
    all_goals
      rw [show Address.rename (renameVertex (Equiv.refl (Fin _))) = id from funext (rename_refl _),
        List.map_id_fun]
      rfl

private theorem compare_label (eval : KindEvaluator Op G) {left right : NodeLabel Op}
    (same : left = right)
    (runLeft : Fin left.arity → Tuple G left.kind.entry → Option (Tuple G left.kind.exit))
    (runRight : Fin right.arity → Tuple G right.kind.entry → Option (Tuple G right.kind.exit))
    (input : Option (Tuple G left.ins)) (input' : Option (Tuple G right.ins))
    (equalInputs : input.map colours = input'.map colours)
    (children : ∀ arm arg arg', colours arg = colours arg' →
      (runLeft arm arg).map colours =
        (runRight (Fin.cast (congrArg NodeLabel.arity same) arm) arg').map colours) :
    (input >>= eval left.kind runLeft).map colours =
      (input' >>= eval right.kind runRight).map colours := by
  subst right
  have equal := option_colours_injective equalInputs
  subst input'
  obtain ⟨ins, outs, kind⟩ := left
  have runners : runLeft = runRight := by
    funext arm entry
    exact option_colours_injective (children arm entry entry rfl)
  rw [runners]

private theorem run_colours {argsL argsR outsL outsR : Ports (PortType V S)}
    {sigsL sigsR : List (Ports (PortType V S))}
    {left : Graph Op argsL [] sigsL outsL} {right : Graph Op argsR [] sigsR outsR}
    (iso : Graph.Isomorphic Op left right) (eval : KindEvaluator Op G)
    (inputL : Tuple G argsL) (inputR : Tuple G argsR)
    (inputEq : colours inputL = colours inputR) :
    (left.evalWith eval inputL PUnit.unit).map colours = (right.evalWith eval inputR PUnit.unit).map colours := by
  classical
  induction iso with
  | @intro argsL argsR outsL outsR sigsL sigsR left right _ _ ids labels inputs results _ childIH =>
    let allL := store (graphTrace eval left inputL)
    let allR := store (graphTrace eval right inputR)
    have vertices (n : Nat) (valid : n < sigsL.length) :
        allL[n]? = allR[renameVertex ids n]? := by
      induction n using Nat.strongRecOn with
      | ind n earlier =>
        let i : Fin sigsL.length := ⟨n, valid⟩
        obtain ⟨beforeL, prefL, atL⟩ := graphTrace_at eval left inputL i
        obtain ⟨beforeR, prefR, atR⟩ := graphTrace_at eval right inputR (ids i)
        simp only [renameVertex, dite_eq_left valid]
        change allL[i.val]? = allR[(ids i).val]?
        rw [atL, atR]
        apply congrArg some
        refine compare_label eval (labels i) _ _ _ _ ?_ (childIH i)
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

theorem evalWith_eq {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (eval : KindEvaluator Op G)
    (entry : Tuple G args) : left.evalWith eval entry PUnit.unit = right.evalWith eval entry PUnit.unit :=
  option_colours_injective (run_colours iso eval entry entry rfl)

private theorem total_table (m : Model.{u,v,w} Op) (fuel : Nat) (entry : Tuple m.Val args)
    (past sigs : List (Ports (PortType V S))) (locals : Locals m.Val past)
    (nodes : Nodes Op args past sigs) (children : Runners m nodes)
    (results : Wires args (extend past sigs) outs) :
    evalTableWith (Kind.eval m fuel) entry past sigs locals nodes children results =
      evalTable m fuel entry past sigs locals nodes children results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    simp only [evalTableWith, evalTable]
    congr 1
    funext result
    exact ih _ _ _ _ _

private theorem total_graph (m : Model.{u,v,w} Op) (fuel : Nat)
    {past : List (Ports (PortType V S))} (g : Graph Op args past sigs outs)
    (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    g.evalWith (Kind.eval m fuel) entry locals = g.eval m fuel entry locals := by
  induction g with
  | region nodes children results ih =>
    simp only [Graph.evalWith, Graph.eval, total_table]
    congr 1
    funext i j input
    exact ih i j input PUnit.unit

theorem run_eq {left : Graph Op args [] sigs outs} {right : Graph Op args [] sigs' outs}
    (iso : Graph.Isomorphic Op left right) (m : Model.{u, v, w} Op) (fuel : Nat)
    (entry : Tuple m.Val args) : left.run m fuel entry = right.run m fuel entry := by
  exact (total_graph m fuel left entry PUnit.unit).symm.trans
    ((evalWith_eq iso (Kind.eval m fuel) entry).trans (total_graph m fuel right entry PUnit.unit))

end Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Proofs
