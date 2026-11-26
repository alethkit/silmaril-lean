module

public import Silmaril.SSA.PEG.Scope

public section

namespace Silmaril.SSA.PEG.Proofs

open RVSDG (Port Tuple)

universe u v w x y

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results : List (Ty Data)} {n n' l l' : Nat}

private theorem reindexRefs_refl {s : Fin n → Ty Data} {ts : List (Ty Data)}
    (xs : Tuple (Ref s) ts) :
    xs.map (fun _ r => r.reindex (Equiv.refl _)) = xs := by
  induction xs with
  | nil => rfl
  | cons r _ ih => rw [Tuple.map, ih]; cases r; rfl

private theorem reindexForest_refl (forest : LoopForest l) :
    forest.reindex (Equiv.refl _) = forest := by
  cases forest with
  | mk parent =>
    change LoopForest.mk (fun i => (parent i).map id) = LoopForest.mk parent
    congr
    funext i
    cases parent i <;> rfl

private theorem label_map_id {L : Type} {ts : List (Ty Data)} {out : Ty Data}
    (op : Label P params L ts out) : op.map (fun instr => instr) id = op := by
  cases op <;> rfl

private theorem label_map_comp {R : InstructionSet.{u,y} Data} {L : Type}
    {ts : List (Ty Data)} {out : Ty Data} (op : Label P params L ts out)
    (f : InstructionMap P Q) (g : InstructionMap Q R) :
    (op.map f id).map g id = op.map (fun instr => g (f instr)) id := by
  cases op <;> rfl

private theorem mapOps_table (g : Graph P params results n l) (f : InstructionMap P Q) :
    g.mapOps f = ⟨g.forest, g.sort, fun i =>
      ⟨(g.node i).inputs, (g.node i).label.map f id, (g.node i).args⟩, g.roots⟩ := by
  simp only [Graph.mapOps, Graph.relabel, Node.relabel, Equiv.refl_symm, reindexForest_refl]
  exact congrArg₂ (fun (nodes : ∀ i, Node Q params (Fin l) g.sort (g.sort i)) roots =>
    (⟨g.forest, g.sort, nodes, roots⟩ : Graph Q params results n l))
    (funext fun i => congrArg (Node.mk _ _) (reindexRefs_refl (g.node i).args))
    (reindexRefs_refl g.roots)

theorem mapOps_id (g : Graph P params results n l) : g.mapOps (fun op => op) = g := by
  rw [mapOps_table]
  simp [label_map_id]

theorem mapOps_comp {R : InstructionSet.{u,y} Data} (g : Graph P params results n l)
    (f : InstructionMap P Q) (h : InstructionMap Q R) :
    (g.mapOps f).mapOps h = g.mapOps (fun op => h (f op)) := by
  simp only [mapOps_table, label_map_comp]

private theorem get_map {Ty : Type u} {F : Ty → Type v} {G : Ty → Type w}
    (f : ∀ t, F t → G t) {ts : List Ty} {t : Ty} (p : Port ts t) (xs : Tuple F ts) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail p ih =>
    cases xs with
    | cons _ xs => exact ih xs

theorem arg_relabel {s : Fin n → Ty Data} {out : Ty Data} {L L' : Type}
    (node : Node P params L s out) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : L → L') (i : Fin node.inputs.length) :
    (node.relabel f ids loops).arg i = (node.arg i).reindex ids :=
  get_map _ _ _

theorem root_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) {out : Ty Data} (p : Port results out) :
    (g.relabel f ids loops).roots.get p = (g.roots.get p).reindex ids :=
  get_map _ _ _

private theorem kind_map {L L' : Type} {ins : List (Ty Data)} {out : Ty Data}
    (a : Label P params L ins out) (f : InstructionMap P Q) (loops : L → L')
    (i : Fin ins.length) : (a.map f loops).kind i = (a.kind i).map loops := by
  cases a <;> try rfl
  all_goals by_cases h : i.val = 0 <;> simp [Label.map, Label.kind, EdgeKind.map, h]

theorem mapKind_inv {L L' : Type} (e : L ≃ L') (k : EdgeKind L) :
    (k.map e).map e.symm = k := by
  cases k <;> simp [EdgeKind.map]

theorem mapKind_symm_inv {L L' : Type} (e : L ≃ L') (k : EdgeKind L') :
    (k.map e.symm).map e = k := by
  cases k <;> simp [EdgeKind.map]

theorem edge_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l)
    (a b : Fin n') (k : EdgeKind (Fin l')) :
    (g.relabel f ids loops).Edge a k b ↔ g.Edge (ids a) (k.map loops) (ids b) := by
  change (∃ i, ((g.node (ids a)).label.map f loops.symm).kind i = k ∧
    (((g.node (ids a)).relabel f ids loops.symm).arg i).id = b) ↔ _
  simp only [Graph.Edge, kind_map, arg_relabel, Ref.reindex]
  constructor
  · rintro ⟨i, hk, hb⟩
    refine ⟨i, ?_, ?_⟩
    · simpa only [mapKind_symm_inv] using congrArg (EdgeKind.map loops) hk
    · simpa only [Equiv.apply_symm_apply] using congrArg ids hb
  · rintro ⟨i, hk, hb⟩
    exact ⟨i, by rw [hk]; exact mapKind_inv loops k, by simp [hb]⟩

theorem mapWalk {V : Type u} {K : Type v} {V' : Type w} {K' : Type x}
    {e : V → K → V → Prop} {e' : V' → K' → V' → Prop}
    (f : V → V') (g : K → K') (step : ∀ {a b k}, e a k b → e' (f a) (g k) (f b))
    {a b : V} {ks : List K} (h : Walk e a ks b) : Walk e' (f a) (ks.map g) (f b) := by
  induction h with
  | nil a => exact .nil (f a)
  | cons edge _ ih => exact .cons (step edge) ih

theorem walk_preserves {V : Type u} {K : Type v} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (h : Walk e a ks b) {p : V → Prop}
    (step : ∀ {x y k}, e x k y → k ∈ ks → p x → p y) (ha : p a) : p b := by
  induction h with
  | nil _ => exact ha
  | cons edge _ ih =>
    exact ih (fun hxy hk => step hxy (List.mem_cons_of_mem _ hk))
      (step edge List.mem_cons_self ha)

theorem walk_strictRank {V : Type u} {K : Type v} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (walk : Walk e a ks b) (nonempty : ks ≠ []) (rank : V → Nat)
    (step : ∀ {x y k}, e x k y → k ∈ ks → rank y < rank x) : rank b < rank a := by
  cases walk with
  | nil => exact (nonempty rfl).elim
  | cons edge tail =>
    exact walk_preserves tail
      (fun e hk h => Nat.lt_trans (step e (List.mem_cons_of_mem _ hk)) h)
      (step edge List.mem_cons_self)

end Silmaril.SSA.PEG.Proofs
