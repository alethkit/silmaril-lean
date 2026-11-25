module

public import Silmaril.SSA.RVSDG.MLIR.Regionless.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
public import Silmaril.SSA.MLIR.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.Regionless.Proofs

open CategoryTheory

variable {V St : Type} {P Q : Dialect V St} {L K : Silmaril.MLIR.Institution.Signature false}
variable {F G : PortType V St → Type}

private theorem tuple_get_map (f : ∀ t, F t → G t) {ts : Ports (PortType V St)}
    (xs : Tuple F ts) {t : PortType V St} (p : Port ts t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ xs => exact ih xs

private def mapLocals (f : ∀ t, F t → G t) :
    (past : List (Ports (PortType V St))) → Locals F past → Locals G past
  | [], _ => PUnit.unit
  | _ :: tail, xs => (xs.1.map f, mapLocals f tail xs.2)

private theorem locals_get_map (f : ∀ t, F t → G t)
    (past : List (Ports (PortType V St))) (xs : Locals F past) (i : Fin past.length) :
    (mapLocals f past xs).get i = (xs.get i).map f := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih xs.2 j) i

private theorem locals_snoc_map (f : ∀ t, F t → G t)
    (past : List (Ports (PortType V St))) (xs : Locals F past)
    {head : Ports (PortType V St)} (x : Tuple F head) :
    mapLocals f (past ++ [head]) (xs.snoc x) = (mapLocals f past xs).snoc (x.map f) := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Prod.mk _) (ih xs.2)

private theorem read_map (f : ∀ t, F t → G t) {args outs : Ports (PortType V St)}
    {past : List (Ports (PortType V St))} (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    (wires.read entry locals).map f = wires.read (entry.map f) (mapLocals f past locals) := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      exact congrArg₂ Tuple.cons (tuple_get_map f entry p).symm ih
    | output i p =>
      have h : ((mapLocals f past locals).get i).get p = f _ ((locals.get i).get p) := by
        rw [locals_get_map, tuple_get_map]
      exact congrArg₂ Tuple.cons h.symm ih

-- The evaluator transports along maps of values preserving primitive results and selectors.
set_option backward.isDefEq.respectTransparency false in
private theorem eval_map {m n : Model.{0, 0, 0} P} (f : ∀ t, m.Val t → n.Val t)
    (run : ∀ {ins outs} (op : P ins outs) (input : Tuple m.Val ins),
      (m.run op input).map f = n.run op (input.map f))
    (control : ∀ k (x : ULift (Fin k)), f (.control k) x = x)
    {args outs : Ports (PortType V St)} {past sigs : List (Ports (PortType V St))}
    (term : Term P args past sigs outs) (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    (term.eval m entry locals).map f =
      term.eval n (entry.map f) (mapLocals f past locals) := by
  induction term with
  | ret wires => exact read_map f wires entry locals
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    simp only [Term.eval, ihRest, locals_snoc_map]
    rw [← read_map f wires entry locals]
    congr 2
    cases shape with
    | simple op => exact run op _
    | gamma extra =>
      cases wires.read entry locals with
      | cons choice payload =>
        simp only [Tuple.map, control, Shape.eval]
        exact ihChildren choice.down payload PUnit.unit

private theorem graph_run_map {m n : Model.{0, 0, 0} P} (f : ∀ t, m.Val t → n.Val t)
    (run : ∀ {ins outs} (op : P ins outs) (input : Tuple m.Val ins),
      (m.run op input).map f = n.run op (input.map f))
    (control : ∀ k (x : ULift (Fin k)), f (.control k) x = x)
    {args outs : Ports (PortType V St)} {sigs : List (Ports (PortType V St))}
    (g : Graph P args [] sigs outs) (entry : Tuple m.Val args) :
    (g.run m entry).map f = g.run n (entry.map f) := by
  rw [← Graph.run_toTerm, ← Graph.run_toTerm]
  exact eval_map f run control g.toTerm entry PUnit.unit

theorem to_ofAssignment (ts : List V) (env : (i : Fin ts.length) → F (.value (ts.get i))) :
    toAssignment ts (ofAssignment ts env) = env := by
  induction ts with
  | nil => exact funext fun i => i.elim0
  | cons _ ts ih =>
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrFun (ih (fun i => env i.succ)) j

theorem of_toAssignment (ts : List V) (xs : Tuple F (valuePorts St ts)) :
    ofAssignment ts (toAssignment ts xs) = xs := by
  induction ts with
  | nil => cases xs; rfl
  | cons _ ts ih => cases xs with | cons x xs => exact congrArg (Tuple.cons x) (ih xs)

private theorem toAssignment_map (f : ∀ t, F t → G t)
    (ts : List V) (xs : Tuple F (valuePorts St ts)) (i : Fin ts.length) :
    toAssignment ts (xs.map f) i = f _ (toAssignment ts xs i) := by
  induction ts with
  | nil => exact i.elim0
  | cons _ ts ih =>
    cases xs with
    | cons x xs => exact Fin.cases rfl (ih xs) i

private theorem ofAssignment_map (f : ∀ t, F t → G t)
    (ts : List V) (env : (i : Fin ts.length) → F (.value (ts.get i))) :
    (ofAssignment ts env).map f = ofAssignment ts (fun i => f _ (env i)) := by
  induction ts with
  | nil => rfl
  | cons _ ts ih => exact congrArg (Tuple.cons (f _ (env 0))) (ih (fun i => env i.succ))

open Silmaril.MLIR.Institution (Assignment)

variable {args outs : List V} {sigs : List (Ports (PortType V St))}

private def denotePort (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (env : Assignment M.carrier (context f.sort args)) :
    (t : PortType V St) → (f.syntaxModel args).Val t → (f.pullback M).Val t
  | .value _, t => t.denote M env
  | .state _, x => x
  | .control _, x => x

set_option backward.isDefEq.respectTransparency false in
theorem denote_translateGraph (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs))
    (env : Assignment M.carrier (context f.sort args)) (i : Fin outs.length) :
    (translateGraph f g i).denote M env =
      toAssignment outs (g.run (f.pullback M) (ofAssignment args env)) i := by
  have run := graph_run_map (denotePort f M env) (g := g)
    (entry := ofAssignment args Silmaril.MLIR.Institution.Term.var)
    (control := fun _ _ => rfl) (run := ?_)
  · calc
      _ = toAssignment outs ((g.run (f.syntaxModel args)
          (ofAssignment args Silmaril.MLIR.Institution.Term.var)).map (denotePort f M env)) i :=
        (toAssignment_map (denotePort f M env) outs _ i).symm
      _ = _ := by rw [run, ofAssignment_map]; rfl
  · intro ins outs op input
    simp only [ProfileMap.syntaxModel, ProfileMap.pullback, ProfileMap.interpret]
    generalize f.symbol op = s
    cases s with
    | symbol s =>
      simp only [MatchedOp.interpret]
      rw [ofAssignment_map]
      congr 1
      funext j
      change ((operationBlock s j).subst _).denote M env = _
      rw [Silmaril.MLIR.Institution.Term.denote_subst]
      simp only [operationBlock, Silmaril.MLIR.Institution.Term.denote]
      congr 1
      · funext k
        exact (toAssignment_map (denotePort f M env) _ input k).symm
      · exact funext fun r => r.elim0

set_option backward.isDefEq.respectTransparency false in
theorem satisfaction (f : ProfileMap P L) (M : Silmaril.MLIR.Institution.Model L)
    (e : ValueEquation P) :
    (translateEquation f e).Holds M ↔ e.toRVSDG.Holds (f.pullback M) := by
  change (∀ env, ∀ i, (translateGraph f e.lhs i).denote M env =
    (translateGraph f e.rhs i).denote M env) ↔ _
  simp only [denote_translateGraph]
  constructor
  · intro h input
    have pointwise := funext (h (toAssignment e.args input))
    rw [of_toAssignment] at pointwise
    exact (of_toAssignment _ _).symm.trans
      ((congrArg (ofAssignment e.outs) pointwise).trans (of_toAssignment _ _))
  · intro h env i
    exact congrArg (fun xs => toAssignment e.outs xs i) (h (ofAssignment e.args env))

set_option backward.isDefEq.respectTransparency false in
theorem translateGraph_precomp (f : ProfileMap Q L) (h : Institution.OpcodeMap P Q)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) :
    translateGraph (f.precomp h) g = translateGraph f (Institution.mapGraph h g) := by
  unfold translateGraph
  rw [Institution.mapGraph_run]
  rfl

private def mapPort (f : ProfileMap P L) (k : L ⟶ K) :
    (t : PortType V St) → (f.syntaxModel args).Val t → ((f.map k).syntaxModel args).Val t
  | .value _, t => t.map k
  | .state _, x => x
  | .control _, x => x

set_option backward.isDefEq.respectTransparency false in
theorem translateGraph_map (f : ProfileMap P L) (k : L ⟶ K)
    (g : Graph P (valuePorts St args) [] sigs (valuePorts St outs)) (i : Fin outs.length) :
    (translateGraph f g i).map k = translateGraph (f.map k) g i := by
  have run := graph_run_map (mapPort f k) (g := g)
    (entry := ofAssignment args Silmaril.MLIR.Institution.Term.var)
    (control := fun _ _ => rfl) (run := ?_)
  · calc
      _ = toAssignment outs ((g.run (f.syntaxModel args)
          (ofAssignment args Silmaril.MLIR.Institution.Term.var)).map (mapPort f k)) i :=
        (toAssignment_map (mapPort f k) outs _ i).symm
      _ = _ := by rw [run, ofAssignment_map]; rfl
  · intro ins outs op input
    simp only [ProfileMap.syntaxModel, ProfileMap.map, ProfileMap.interpret]
    generalize f.symbol op = s
    cases s with
    | symbol s =>
      simp only [MatchedOp.map, MatchedOp.interpret]
      rw [ofAssignment_map]
      congr 1
      funext j
      change ((operationBlock s j).subst _).map k = _
      have block_map : (operationBlock (L := L) s j).map k =
          operationBlock (L := K) (sort := k.sort ∘ f.sort) (k.symbol s) j := by
        simp only [operationBlock, Silmaril.MLIR.Institution.Term.map]
        congr 1
        exact funext fun r => r.elim0
      rw [Silmaril.MLIR.Institution.Term.map_subst, block_map]
      congr 1
      funext l
      exact (toAssignment_map (mapPort f k) _ input l).symm

set_option backward.isDefEq.respectTransparency false in
theorem pullback_map (f : ProfileMap P L) (k : L ⟶ K)
    (M : Silmaril.MLIR.Institution.Model K) :
    (f.map k).pullback M = f.pullback (M.reduct k) := by
  simp only [ProfileMap.pullback, ProfileMap.interpret, ProfileMap.map,
    Silmaril.MLIR.Institution.Model.reduct]
  congr 1
  funext ins outs op input
  cases f.symbol op
  rfl

end Silmaril.SSA.RVSDG.MLIR.Regionless.Proofs
