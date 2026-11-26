module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Proofs

open CategoryTheory
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

section SignatureChange

open Silmaril.MLIR.Institution (Block)

variable {Q R : Source V}

theorem mapSignature_id (P : Source V) : mapSignature (𝟙 P) = 𝟙 (signature P) := by
  change Silmaril.MLIR.Institution.Signature.Hom.mk (S := signature P) (T := signature P)
      id (fun op => Op.map (𝟙 P) op) =
    Silmaril.MLIR.Institution.Signature.Hom.mk id id
  congr 1
  funext a p op
  cases op <;> rfl

theorem mapSignature_comp (h : P ⟶ Q) (k : Q ⟶ R) :
    mapSignature (h ≫ k) = mapSignature h ≫ mapSignature k := by
  change Silmaril.MLIR.Institution.Signature.Hom.mk (S := signature P) (T := signature R)
      id (fun op => Op.map (h ≫ k) op) =
    Silmaril.MLIR.Institution.Signature.Hom.mk (S := signature P) (T := signature R)
      id (fun op => Op.map k (Op.map h op))
  congr 1
  funext a p op
  cases op <;> rfl

theorem model_reduct (h : P ⟶ Q) (m : Model.{0, 0, 0} Q.op) :
    model (Institution.reduct (Institution.Signature.opcodeMap h) m) =
      (model m).reduct (mapSignature h) := by
  unfold model Silmaril.MLIR.Institution.Model.reduct
  congr 1
  funext a p op args bodies
  cases op <;> rfl

private def rename (h : P ⟶ Q) {n : Nat} {Γ : Fin n → Ty V} :
    ∀ t, Expr P Γ t → Expr Q Γ t :=
  fun _ e => e.map (mapSignature h)

private theorem rename_vars (h : P ⟶ Q) :
    (ofAssignment args (F := Expr P args.get) .var).map (rename h) =
      ofAssignment args (F := Expr Q args.get) .var :=
  of_map (rename h) _

private theorem rename_emit_simple (h : P ⟶ Q) (op : P.op ins outs)
    (args : Tuple (Expr P Γ) ins)
    (bodies : Fin (Shape.simple op).regionCount → Block (signature P) (List.get []) (List.get []))
    (bodies' : Fin (Shape.simple (Institution.Signature.opcodeMap h op)).regionCount →
      Block (signature Q) (List.get []) (List.get [])) :
    (emit (Shape.simple op) args bodies).map (rename h) =
      emit (Shape.simple (Institution.Signature.opcodeMap h op)) (args.map (rename h)) bodies' := by
  simp only [emit, of_map, rename, Silmaril.MLIR.Institution.Term.map, mapSignature, Op.map]
  rw [funext (to_map (rename h) args)]
  congr 1
  funext i
  congr 1
  funext r
  exact r.elim0

private theorem rename_emit_gamma (h : P ⟶ Q) (extra : Nat)
    (args : Tuple (Expr P Γ) (.control (extra + 2) :: ins))
    (bodies : Fin (extra + 2) → Block (signature P) ins.get outs.get) :
    (emit (Shape.gamma (entry := ins) (exit := outs) extra) args bodies).map (rename h) =
      emit (Shape.gamma (entry := ins) (exit := outs) extra) (args.map (rename h))
        (fun r i => rename h _ (bodies r i)) := by
  simp only [emit, of_map, rename, Silmaril.MLIR.Institution.Term.map, mapSignature, Op.map]
  rw [funext (to_map (rename h) args)]
  rfl

private theorem rename_lowerTerm (h : P ⟶ Q) (t : Term P.op args past sigs outs)
    (entry : Tuple (Expr P Γ) args) (locals : Locals (Expr P Γ) past) :
    (lowerTerm entry locals t).map (rename h) =
      lowerTerm (entry.map (rename h)) (mapLocals (rename h) locals)
        (Institution.mapTerm (Institution.Signature.opcodeMap h) t) := by
  induction t generalizing n with
  | ret results => exact read_map _ results entry locals
  | bind node children rest childIH restIH =>
    rcases node with ⟨_, shape, wires, childSigs⟩
    cases shape with
    | simple op =>
      rw [lowerTerm, Institution.mapTerm, lowerTerm, restIH, mapLocals_snoc]
      erw [← read_map (rename h) wires entry locals]
      congr 2
      exact rename_emit_simple h op _ _ _
    | gamma extra =>
      rw [lowerTerm, Institution.mapTerm, lowerTerm, restIH, mapLocals_snoc]
      erw [rename_emit_gamma, read_map]
      congr 3
      funext r i
      have hChild := childIH r (ofAssignment _ .var) PUnit.unit
      rw [rename_vars] at hChild
      exact (to_map (rename h) _ i).symm.trans (congrArg (fun result => toAssignment result i) hChild)

theorem lower_map (h : P ⟶ Q) (g : RVSDG.Graph P.op args [] sigs outs) (i : Fin outs.length) :
    lower (Institution.mapGraph (Institution.Signature.opcodeMap h) g) i =
      (lower g i).map (mapSignature h) := by
  unfold lower Institution.mapGraph
  rw [Term.toTerm_toGraph]
  change _ = rename h _ (toAssignment _ i)
  have hTerm := rename_lowerTerm h g.toTerm (Γ := args.get) (ofAssignment _ .var) PUnit.unit
  rw [rename_vars] at hTerm
  exact (congrArg (fun result => toAssignment result i) hTerm.symm).trans (to_map (rename h) _ i)

end SignatureChange

end Silmaril.SSA.RVSDG.MLIR.Graph.Proofs
