module

public import Silmaril.Proofs.SSA.PEG.Simple.While.Rows

public section

namespace Silmaril.SSA.PEG.Simple.WhileProofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params nodes all base left right results : List (Ty Data)} {out : Ty Data}

private def pos (r : Port nodes out) : Nat := (numberPort r).id.val

private theorem pos_tail {t : Ty Data} (r : Port nodes out) :
    pos (Port.tail (s := t) r) = pos r + 1 := rfl

private theorem posLeft (r : Port left out) :
    pos (portLeft (right := right) r) = pos r := by
  induction r with
  | head => rfl
  | tail r ih =>
    change pos (portLeft r) + 1 = pos r + 1
    rw [ih]

private theorem posRight (left : List (Ty Data)) (r : Port right out) :
    pos (portRight left r) = left.length + pos r := by
  induction left with
  | nil => exact (Nat.zero_add _).symm
  | cons t left ih =>
    change pos (portRight left r) + 1 = left.length + 1 + pos r
    omega

private theorem posLocal (p : WhileProgram P params out) {t : Ty Data}
    (r : Port p.core.nodes t) : pos (p.localRef r) = 3 + pos r := by
  change pos (portLeft (right := params) r) + 1 + 1 + 1 = 3 + pos r
  rw [posLeft]
  omega

private theorem posParam (p : WhileProgram P params out) {t : Ty Data}
    (r : Port params t) : pos (p.paramRef r) = 3 + p.core.nodes.length + pos r := by
  change pos (portRight p.core.nodes r) + 1 + 1 + 1 = 3 + p.core.nodes.length + pos r
  rw [posRight]
  omega

private def SafeEdge (a b : Nat) (kind : EdgeKind (Fin 1)) : Prop :=
  3 - b < 3 - a ∨ (3 ≤ a ∧ 3 ≤ b ∧
    (kind = .feedback 0 ∨ ((kind = .ordinary ∨ kind = .initial 0) ∧ a < b)))

private def SafeAt (r : WhileRow P params all out) (a : Nat) : Prop :=
  ∀ slot : Fin r.inputs.length,
    SafeEdge a (pos (r.refs.get (portAt r.inputs slot))) (r.label.kind slot)

private theorem ordinary (label : Label P params (Fin 0) left out) (slot : Fin left.length) :
    (label.map (fun op => op) (Fin.elim0 (α := Fin 1))).kind slot = .ordinary := by
  cases label with
  | op | phi | param => rfl
  | theta impossible | pass impossible | eval impossible => exact impossible.elim0

private theorem closedSafe (code : Code P params base nodes)
    (holes : ∀ {t}, Port base t → WhileRow P params all t)
    (embed : ∀ {t}, Port nodes t → Port all t) (offset : Nat) (low : 3 ≤ offset)
    (addr : ∀ t (r : Port nodes t), pos (embed r) = offset + pos r)
    (safe : ∀ t (r : Port base t), SafeAt (holes r) (pos (embed (code.lift r))))
    (t : Ty Data) (r : Port nodes t) :
    SafeAt (code.closeRows holes embed r) (pos (embed r)) := by
  induction code generalizing offset with
  | empty => exact safe t r
  | emit prior label refs ih =>
    cases r with
    | head =>
      intro slot
      let targetSlot := refs.get (portAt _ slot)
      have target := addr _ (.tail targetSlot)
      rw [pos_tail] at target
      have source : pos (embed .head) = offset := addr _ .head |>.trans (Nat.add_zero _)
      refine .inr ⟨by omega, ?_, .inr ⟨.inl (ordinary label slot), ?_⟩⟩
      · change 3 ≤ pos ((refs.map (fun _ q => embed (.tail q))).get (portAt _ slot))
        rw [Proofs.get_map]
        change 3 ≤ pos (embed (.tail targetSlot))
        omega
      · change pos (embed .head) < pos ((refs.map (fun _ q => embed (.tail q))).get (portAt _ slot))
        rw [Proofs.get_map]
        change pos (embed .head) < pos (embed (.tail targetSlot))
        omega
    | tail q =>
      apply ih (fun r => embed (.tail r)) (offset + 1) (by omega)
      · intro t r
        rw [addr, pos_tail]
        omega
      · exact safe

private theorem thetaSafe (p : WhileProgram P params out) {t : Ty Data}
    (r : Port params t) :
    SafeAt (p.thetaRow r) (pos (p.localRef (p.core.code.lift r))) := by
  intro slot
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) slot
  · have ha := posLocal p (p.core.code.lift r)
    have hb := posParam p r
    have lt : pos (p.core.code.lift r) < p.core.nodes.length := (numberPort (p.core.code.lift r)).id.isLt
    exact .inr ⟨by omega, by
      change 3 ≤ pos (p.paramRef r)
      omega, .inr ⟨.inr rfl, by
      change pos (p.localRef (p.core.code.lift r)) < pos (p.paramRef r)
      omega⟩⟩
  · have ha := posLocal p (p.core.code.lift r)
    have hb := posLocal p (p.core.refs.get (.tail r))
    exact .inr ⟨by omega, by
      change 3 ≤ pos (p.localRef (p.core.refs.get (.tail r)))
      omega, .inl rfl⟩

private theorem rowsSafe (p : WhileProgram P params out) (neg : P [.bool] .bool)
    (t : Ty Data) (r : Port p.layout t) : SafeAt (p.row neg r) (pos r) := by
  cases r with
  | head =>
    intro k
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => z.elim0) j) k
    · left
      change 3 - pos (p.localRef (p.core.code.lift p.retvar)) < 3 - 0
      rw [posLocal]
      omega
    · left
      change 2 < 3
      decide
  | tail r =>
    cases r with
    | head =>
      intro k
      refine Fin.cases ?_ (fun j => j.elim0) k
      left
      change 1 < 2
      decide
    | tail r =>
      cases r with
      | head =>
        intro k
        refine Fin.cases ?_ (fun j => j.elim0) k
        left
        change 3 - pos (p.localRef (p.core.refs.get .head)) < 3 - 2
        rw [posLocal]
        omega
      | tail r =>
        rcases splitCases p.core.nodes r with ⟨q, rfl⟩ | ⟨q, rfl⟩
        · change SafeAt (p.row neg (p.localRef q)) (pos (p.localRef q))
          rw [localRow]
          exact closedSafe p.core.code (p.thetaRow ·) (p.localRef ·) 3 (by decide)
            (fun _ => posLocal p) (fun _ => thetaSafe p) _ q
        · change SafeAt (p.row neg (p.paramRef q)) (pos (p.paramRef q))
          rw [paramRow]
          exact fun k => k.elim0

private theorem edgeCheck (p : WhileProgram P params out) (a b : Fin p.layout.length)
    (kind : EdgeKind (Fin 1))
    (safe : 3 - b.val < 3 - a.val ∨ (3 ≤ a.val ∧ 3 ≤ b.val ∧
      (kind = .feedback 0 ∨ ((kind = .ordinary ∨ kind = .initial 0) ∧ a.val < b.val)))) :
    p.rank.checkEdge a b kind = true := by
  rcases safe with drop | ⟨ha, hb, reason⟩
  · simp [WhileProgram.rank, DemandRank.checkEdge, RankComponent.change, drop]
  · have flatA : 3 - a.val = 0 := by omega
    have flatB : 3 - b.val = 0 := by omega
    rcases reason with rfl | ⟨plain, forward⟩
    · simp [WhileProgram.rank, DemandRank.checkEdge, RankComponent.change, flatA, flatB]
    · have drop : p.layout.length - b.val < p.layout.length - a.val := by omega
      rcases plain with rfl | rfl <;>
        simp [WhileProgram.rank, DemandRank.checkEdge, RankComponent.change, flatA, flatB, drop]

private theorem safeOperand (p : WhileProgram P params out) (neg : P [.bool] .bool)
    (a : Fin p.layout.length) (slot : Fin ((p.translate neg).node a).inputs.length) :
    SafeEdge a.val (((p.translate neg).node a).arg slot).id.val
      (((p.translate neg).node a).label.kind slot) := by
  let r := p.row neg (portAt p.layout a)
  change SafeEdge a.val ((r.refs.map (fun _ q => numberPort q)).get (portAt r.inputs slot)).id.val
    (r.label.kind slot)
  rw [Proofs.get_map]
  have h := rowsSafe p neg _ (portAt p.layout a) slot
  change SafeEdge (pos (portAt p.layout a)) (pos (r.refs.get (portAt r.inputs slot)))
    (r.label.kind slot) at h
  simpa only [pos, Proofs.number_portAt] using h

theorem checkRank (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    p.rank.check (p.translate neg) = true := by
  unfold DemandRank.check
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro slot _
  exact edgeCheck p a _ _ (safeOperand p neg a slot)

private theorem safeEdge (p : WhileProgram P params out) (neg : P [.bool] .bool)
    {a b : Fin p.layout.length} {kind : EdgeKind (Fin 1)}
    (edge : (p.translate neg).Edge a kind b) : SafeEdge a.val b.val kind := by
  obtain ⟨slot, rfl, rfl⟩ := edge
  exact safeOperand p neg a slot

private theorem safePhase {a b : Nat} {kind : EdgeKind (Fin 1)} (h : SafeEdge a b kind) :
    3 - b ≤ 3 - a ∧ (∀ l, kind.IsObserverAt l → 3 - b < 3 - a) := by
  rcases h with drop | ⟨ha, hb, reason⟩
  · exact ⟨Nat.le_of_lt drop, fun _ _ => drop⟩
  refine ⟨by omega, ?_⟩
  intro l witness
  rcases reason with rfl | ⟨rfl | rfl, _⟩ <;> cases witness <;> contradiction

private theorem walkPhase (p : WhileProgram P params out) (neg : P [.bool] .bool)
    {a b : Fin p.layout.length} {ks : List (EdgeKind (Fin 1))}
    (walk : Walk (p.translate neg).Edge a ks b) :
    3 - b.val ≤ 3 - a.val ∧
      (∀ k ∈ ks, ∀ l, k.IsObserverAt l → 3 - b.val < 3 - a.val) := by
  induction walk with
  | nil a => exact ⟨Nat.le_refl _, by simp⟩
  | cons edge _ ih =>
    have phase := safePhase (safeEdge p neg edge)
    refine ⟨Nat.le_trans ih.1 phase.1, ?_⟩
    intro k member l observer
    rcases List.mem_cons.mp member with rfl | rest
    · exact Nat.lt_of_le_of_lt ih.1 (phase.2 l observer)
    · exact Nat.lt_of_lt_of_le (ih.2 k rest l observer) phase.1

theorem wellFormed (p : WhileProgram P params out) (neg : P [.bool] .bool) :
    (p.translate neg).WellFormed where
  forest := by
    rintro i ⟨ks, walk, nonempty⟩
    cases walk with
    | nil => exact nonempty rfl
    | cons edge _ => cases edge
  feedback := by
    intro a ks walk nonempty
    by_contra missing
    have decreases := walk.strictRank nonempty (fun i => p.layout.length - i.val) (fun {x y kind} edge member => by
      have yBound := y.isLt
      have nonfeedback := fun h => missing ⟨_, member, h⟩
      rcases safeEdge p neg edge with drop | ⟨_, _, rfl | ⟨_, forward⟩⟩
      · omega
      · exact (nonfeedback trivial).elim
      · omega)
    exact Nat.lt_irrefl _ decreases
  loopScope := by
    intro _ _ _ start target _ _ _
    have same : target = start := Subsingleton.elim _ _
    subst target
    exact .inl ⟨[], .nil start⟩
  outerFeedback := by
    intro a ks walk k member inner observer
    exact (Nat.lt_irrefl _ ((walkPhase p neg walk).2 k member inner observer)).elim

end Silmaril.SSA.PEG.Simple.WhileProofs
