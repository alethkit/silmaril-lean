module

public import Silmaril.Proofs.SSA.PEG.Graph

public section

namespace Silmaril.SSA.PEG.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results : List (Ty Data)} {n n' l l' : Nat}

private theorem loop_map {L L' : Type} {ins : List (Ty Data)} {out : Ty Data}
    (a : Label P params L ins out) (f : InstructionMap P Q) (loops : L → L') :
    (a.map f loops).loop = a.loop.map loops := by cases a <;> rfl

private theorem theta_map {L L' : Type} {ins : List (Ty Data)} {out : Ty Data}
    (a : Label P params L ins out) (f : InstructionMap P Q) (loops : L → L') :
    (a.map f loops).thetaLoop = a.thetaLoop.map loops := by cases a <;> rfl

private theorem mapOption_inv {α β : Type} (f : α ≃ β) (o : Option α) :
    (o.map f).map f.symm = o := by cases o <;> simp

private structure ScopeIso (A : Graph P params results n l) (B : Graph Q params results n' l') where
  vertices : Fin n ≃ Fin n'
  loops : Fin l ≃ Fin l'
  edge : ∀ a k b, A.Edge a k b ↔ B.Edge (vertices a) (k.map loops) (vertices b)
  parent : ∀ i, (A.forest.parent i).map loops = B.forest.parent (loops i)
  loop : ∀ a, (A.node a).label.loop.map loops = (B.node (vertices a)).label.loop
  theta : ∀ a, (A.node a).label.thetaLoop.map loops = (B.node (vertices a)).label.thetaLoop

variable {A : Graph P params results n l} {B : Graph Q params results n' l'}

private def ScopeIso.symm (e : ScopeIso A B) : ScopeIso B A where
  vertices := e.vertices.symm
  loops := e.loops.symm
  edge a k b := by
    simpa only [Equiv.apply_symm_apply, mapKind_symm_inv] using
      (e.edge (e.vertices.symm a) (k.map e.loops.symm) (e.vertices.symm b)).symm
  parent i := by
    have h := congrArg (Option.map e.loops.symm) (e.parent (e.loops.symm i))
    simpa only [Equiv.apply_symm_apply, mapOption_inv] using h.symm
  loop a := by
    have h := (e.loop (e.vertices.symm a)).trans
      (congrArg (fun i => (B.node i).label.loop) (e.vertices.apply_symm_apply a))
    simpa only [mapOption_inv] using (congrArg (Option.map e.loops.symm) h).symm
  theta a := by
    have h := (e.theta (e.vertices.symm a)).trans
      (congrArg (fun i => (B.node i).label.thetaLoop) (e.vertices.apply_symm_apply a))
    simpa only [mapOption_inv] using (congrArg (Option.map e.loops.symm) h).symm

private def scopeIsoRelabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) : ScopeIso (g.relabel f ids loops) g where
  vertices := ids
  loops := loops
  edge a k b := edge_relabel g f ids loops a b k
  parent i := mapOption_inv loops.symm (g.forest.parent (loops i))
  loop a := (congrArg (Option.map loops) (loop_map (g.node (ids a)).label f loops.symm)).trans
    (mapOption_inv loops.symm _)
  theta a := (congrArg (Option.map loops) (theta_map (g.node (ids a)).label f loops.symm)).trans
    (mapOption_inv loops.symm _)

private theorem ScopeIso.up (e : ScopeIso A B) {a b : Fin l} {k : Unit}
    (h : A.forest.Up a k b) : B.forest.Up (e.loops a) k (e.loops b) := by
  unfold LoopForest.Up at *
  rw [← e.parent, h]
  rfl

private theorem ScopeIso.upWalk (e : ScopeIso A B) {a b : Fin l} {ks : List Unit}
    (h : Walk A.forest.Up a ks b) : Walk B.forest.Up (e.loops a) ks (e.loops b) := by
  simpa using mapWalk e.loops id (fun h => e.up h) h

private theorem ScopeIso.encloses (e : ScopeIso A B) {a b : Fin l'}
    (h : B.forest.Encloses a b) : A.forest.Encloses (e.loops.symm a) (e.loops.symm b) :=
  let ⟨ks, path⟩ := h
  ⟨ks, e.symm.upWalk path⟩

private theorem ScopeIso.strictlyEncloses (e : ScopeIso A B) {a b : Fin l'}
    (h : B.forest.StrictlyEncloses a b) :
    A.forest.StrictlyEncloses (e.loops.symm a) (e.loops.symm b) :=
  let ⟨ks, path, pos⟩ := h
  ⟨ks, e.symm.upWalk path, pos⟩

private theorem mem_map_kind {L L' : Type} (e : L ≃ L') {ks : List (EdgeKind L)}
    {k : EdgeKind L'} (h : k ∈ ks.map (EdgeKind.map e)) : k.map e.symm ∈ ks := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
  simpa only [mapKind_inv] using hk

private theorem ScopeIso.wellFormed (e : ScopeIso A B) (h : B.WellFormed) : A.WellFormed where
  forest := by
    intro i
    rintro ⟨ks, path, pos⟩
    exact h.forest (e.loops i) ⟨ks, e.upWalk path, pos⟩
  feedback := by
    intro a ks path pos
    have path' := mapWalk e.vertices (EdgeKind.map e.loops) (fun h => (e.edge _ _ _).mp h) path
    obtain ⟨k, hk, feedback⟩ := h.feedback _ _ path' (by simpa using pos)
    cases k <;> simp only [EdgeKind.IsFeedback] at feedback
    case feedback j =>
      exact ⟨.feedback (e.loops.symm j), mem_map_kind e.loops hk, trivial⟩
  loopScope := by
    intro a b ks start target path ha hb
    have path' := mapWalk e.vertices (EdgeKind.map e.loops) (fun h => (e.edge _ _ _).mp h) path
    have ha' : (B.node (e.vertices a)).label.loop = some (e.loops start) := by rw [← e.loop, ha]; rfl
    have hb' : (B.node (e.vertices b)).label.thetaLoop = some (e.loops target) := by
      rw [← e.theta, hb]; rfl
    rcases h.loopScope _ _ _ _ _ path' ha' hb' with encloses | sampled
    · exact .inl (by simpa using e.encloses encloses)
    · exact .inr (by simpa [EdgeKind.map] using mem_map_kind e.loops sampled)
  outerFeedback := by
    intro a ks path k hk inner obs
    have path' := mapWalk e.vertices (EdgeKind.map e.loops) (fun h => (e.edge _ _ _).mp h) path
    have obs' : (k.map e.loops).IsObserverAt (e.loops inner) := by
      rcases obs with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    obtain ⟨outer, encloses, back⟩ :=
      h.outerFeedback _ _ path' _ (List.mem_map_of_mem hk) _ obs'
    exact ⟨e.loops.symm outer, by simpa using e.strictlyEncloses encloses,
      mem_map_kind e.loops back⟩

theorem wellFormed_relabel (g : Graph P params results n l) (f : InstructionMap P Q)
    (ids : Fin n' ≃ Fin n) (loops : Fin l' ≃ Fin l) :
    (g.relabel f ids loops).WellFormed ↔ g.WellFormed :=
  let e := scopeIsoRelabel g f ids loops
  ⟨e.symm.wellFormed, e.wellFormed⟩

theorem paperWellFormed_of_wellFormed (g : Graph P params results n l) (wf : g.WellFormed) :
    g.PaperWellFormed where
  forest := wf.forest
  feedback := wf.feedback
  loopScope := wf.loopScope
  outerTheta := by
    intro a ks path k hk inner obs
    obtain ⟨outer, encloses, back⟩ := wf.outerFeedback a ks path k hk inner obs
    exact ⟨outer, encloses, .feedback outer, back, .inr rfl⟩

end Silmaril.SSA.PEG.Proofs
