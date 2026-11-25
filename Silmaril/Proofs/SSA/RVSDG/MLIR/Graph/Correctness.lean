module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Proofs

open RVSDG (Locals Shape Term Tuple Wires)

variable {V : Type} {P : Source V} {F G : Ty V → Type}
variable {args ins outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

private theorem of_to (xs : Tuple F args) : ofAssignment args (toAssignment xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (Tuple.cons x) ih

private theorem to_of (env : (i : Fin args.length) → F (args.get i)) (i : Fin args.length) :
    toAssignment (ofAssignment args env) i = env i := by
  induction args with
  | nil => exact i.elim0
  | cons _ ts ih => exact Fin.cases (motive := fun j =>
      toAssignment (ofAssignment (_ :: ts) env) j = env j) rfl (fun j => ih _ j) i

private theorem to_map (f : ∀ t, F t → G t) (xs : Tuple F args) (i : Fin args.length) :
    toAssignment (xs.map f) i = f _ (toAssignment xs i) := by
  induction xs with
  | nil => exact i.elim0
  | cons x xs ih =>
    exact Fin.cases (motive := fun j =>
      toAssignment ((Tuple.cons x xs).map f) j = f _ (toAssignment (Tuple.cons x xs) j)) rfl ih i

private theorem of_map (f : ∀ t, F t → G t) (env : (i : Fin args.length) → F (args.get i)) :
    (ofAssignment args env).map f = ofAssignment args (fun i => f _ (env i)) := by
  induction args with
  | nil => rfl
  | cons _ ts ih => exact congrArg (Tuple.cons (f _ (env 0))) (ih _)

private def mapLocals (f : ∀ t, F t → G t) : {past : List (Ports (Ty V))} →
    Locals F past → Locals G past
  | [], _ => PUnit.unit
  | _ :: _, xs => (xs.1.map f, mapLocals f xs.2)

private theorem mapLocals_get (f : ∀ t, F t → G t) (xs : Locals F past) (i : Fin past.length) :
    (mapLocals f xs).get i = (xs.get i).map f := by
  induction past with
  | nil => exact i.elim0
  | cons _ tail ih => exact Fin.cases (motive := fun j =>
      (mapLocals f xs).get j = (xs.get j).map f) rfl (fun j => ih xs.2 j) i

private theorem mapLocals_snoc (f : ∀ t, F t → G t) (xs : Locals F past) (x : Tuple F outs) :
    mapLocals f (xs.snoc x) = (mapLocals f xs).snoc (x.map f) := by
  induction past with
  | nil => rfl
  | cons _ tail ih => exact congrArg (Prod.mk (xs.1.map f)) (ih xs.2)

private theorem get_map (f : ∀ t, F t → G t) (xs : Tuple F args) {t : Ty V} (p : Port args t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem read_map (f : ∀ t, F t → G t) (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    (wires.read entry locals).map f = wires.read (entry.map f) (mapLocals f locals) := by
  induction wires with
  | nil => rfl
  | cons wire tail ih =>
    cases wire with
    | arg p =>
      simp only [Wires.read, Tuple.map] at ih ⊢
      rw [get_map, ih]
    | output i p =>
      simp only [Wires.read, Tuple.map] at ih ⊢
      rw [mapLocals_get, get_map, ih]

variable (m : Model.{0, 0, 0} P.op) {n : Nat} {Γ : Fin n → Ty V}

private def denote (env : (i : Fin n) → m.Val (Γ i)) :
    ∀ t, Expr P Γ t → m.Val t :=
  fun _ e => e.denote (model m) env

private theorem denote_emit (shape : Shape P.op ins outs)
    (operands : Tuple (Expr P Γ) ins)
    (bodies : (r : Fin shape.regionCount) →
      Silmaril.MLIR.Institution.Block (signature P) shape.entry.get shape.exit.get)
    (env : (i : Fin n) → m.Val (Γ i)) :
    (emit shape operands bodies).map (denote m env) =
      shape.eval m (fun r input => ofAssignment _ (fun i =>
        denote m (toAssignment input) _ (bodies r i))) (operands.map (denote m env)) := by
  cases shape with
  | @simple ins outs op =>
    rw [emit, of_map]
    change ofAssignment outs (toAssignment (m.run op (ofAssignment ins
      (fun i => denote m env _ (toAssignment operands i))))) = m.run op (operands.map (denote m env))
    rw [← (funext (to_map (denote m env) operands)), of_to, of_to]
  | gamma extra =>
    cases operands with
    | cons choice payload =>
      rw [emit, of_map]
      let arm := bodies (denote m env _ choice).down
      change ofAssignment outs (fun i =>
        denote m (fun j => denote m env _ (toAssignment payload j)) _ (arm i)) =
        ofAssignment outs (fun i => denote m (toAssignment (payload.map (denote m env))) _ (arm i))
      rw [funext (to_map (denote m env) payload)]

private theorem denote_vars (input : Tuple m.Val args) :
    (ofAssignment args (F := Expr P args.get) .var).map (denote m (toAssignment input)) = input := by
  rw [of_map]
  exact of_to input

private theorem denote_lowerTerm (t : Term P.op args past sigs outs)
    (entry : Tuple (Expr P Γ) args) (locals : Locals (Expr P Γ) past)
    (env : (i : Fin n) → m.Val (Γ i)) :
    (lowerTerm entry locals t).map (denote m env) =
      t.eval m (entry.map (denote m env)) (mapLocals (denote m env) locals) := by
  induction t generalizing n with
  | ret results => exact read_map _ results entry locals
  | bind node children rest childIH restIH =>
    rw [lowerTerm, Term.eval, restIH, mapLocals_snoc, denote_emit, read_map]
    congr 2
    apply congrArg (fun run => node.shape.eval m run _)
    funext r input
    rw [← funext (to_map _ _), of_to]
    have h := childIH r (Γ := node.shape.entry.get) (ofAssignment _ .var)
      PUnit.unit (toAssignment input)
    rwa [denote_vars] at h

theorem denote_lower (g : RVSDG.Graph P.op args [] sigs outs) (input : Tuple m.Val args) :
    ofAssignment outs (fun i => (lower g i).denote (model m) (toAssignment input)) =
      g.run m input := by
  rw [← RVSDG.Graph.run_toTerm, Term.run]
  change ofAssignment outs (fun i => denote m (toAssignment input) _
    (toAssignment (lowerTerm (past := []) (ofAssignment args .var) PUnit.unit g.toTerm) i)) = _
  rw [← funext (to_map _ _), of_to]
  have h := denote_lowerTerm m (Γ := args.get) g.toTerm (ofAssignment _ .var)
    PUnit.unit (toAssignment input)
  rwa [denote_vars] at h

end Silmaril.SSA.RVSDG.MLIR.Graph.Proofs
