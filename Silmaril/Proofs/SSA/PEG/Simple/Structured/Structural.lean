module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.CompilerScope

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params all ins : List (Ty Data)} {t : Ty Data} {n : Nat}

private theorem thetaOfFeedback (label : Label P params (Fin n) ins t)
    (slot : Fin ins.length) (l : Fin n) (h : label.kind slot = .feedback l) :
    label.thetaLoop = some l := by
  cases label with
  | param | op | phi | pass => cases h
  | theta loop =>
    simp only [Label.kind] at h
    split at h
    · cases h
    · cases h
      rfl
  | eval loop =>
    simp only [Label.kind] at h
    split at h <;> cases h

private theorem loopOfObserver (label : Label P params (Fin n) ins t)
    (slot : Fin ins.length) (l : Fin n) (h : (label.kind slot).IsObserverAt l) :
    label.loop = some l := by
  rcases h with sample | index
  · cases label with
    | param | op | phi => cases sample
    | theta loop =>
      simp only [Label.kind] at sample
      split at sample <;> cases sample
    | eval loop =>
      simp only [Label.kind] at sample
      split at sample
      · cases sample
        rfl
      · cases sample
    | pass loop =>
      cases sample
      rfl
  · cases label with
    | param | op | phi | pass => cases index
    | theta loop =>
      simp only [Label.kind] at index
      split at index <;> cases index
    | eval loop =>
      simp only [Label.kind] at index
      split at index
      · cases index
      · cases index
        rfl

private structure EdgeFacts (catalog : List (Region n)) (a : Fin n) (k : EdgeKind (Fin n))
    (b : Fin n) : Prop where
  region : ∀ f ∈ catalog, f.Contains b.val → f.Contains a.val ∨ k = .sample f.pass
  observer : ∀ l, k.IsObserverAt l → ∃ f ∈ catalog, f.pass = l
  feedback : ∀ l, k = .feedback l → ∃ f ∈ catalog, f.pass = l ∧ f.Contains a.val
  index : ∀ l, k = .index l → b.val = l.val

variable {code : Code P params [] all} {roots : Tuple (RVSDG.Port all) [t]}

private theorem edgeFacts
    (good : GoodRows (regions code (fun r => r) 0 none) (fun r => r)
      (code.rows (fun r => nomatch r) (fun r => r) none))
    {a b : Fin all.length} {k : EdgeKind (Fin all.length)}
    (edge : (code.toGraph roots).Edge a k b) :
    EdgeFacts (regions code (fun r => r) 0 none) a k b := by
  obtain ⟨slot, rfl, rfl⟩ := edge
  let row : Row P params all all[a] := code.rows (fun r => nomatch r) (fun r => r) none (portAt all a)
  have atRow : GoodRow (regions code (fun r => r) 0 none) row a.val := by
    have h := good _ (portAt all a)
    simpa only [pos, Simple.Proofs.number_portAt] using h
  have dest : (((code.toGraph roots).node a).arg slot).id.val =
      pos (row.refs.get (portAt row.inputs slot)) := by
    change (((row.refs.map fun _ p => numberPort p).get (portAt row.inputs slot)).id.val) = _
    rw [Simple.Proofs.get_map]
    rfl
  constructor
  · intro f mem h
    rw [dest] at h
    exact atRow.edge slot f mem h
  · intro l h
    obtain ⟨f, mem, pass, _⟩ := atRow.origin l (loopOfObserver row.label slot l h)
    exact ⟨f, mem, pass⟩
  · intro l h
    exact atRow.theta l (thetaOfFeedback row.label slot l h)
  · intro l h
    rw [dest]
    exact atRow.index slot l h

private theorem structuralScope
    (good : GoodRows (regions code (fun r => r) 0 none) (fun r => r)
      (code.rows (fun r => nomatch r) (fun r => r) none)) :
    (code.toGraph roots).Scoped := by
  classical
  intro a b ks start target path starts ends
  by_cases crossed : EdgeKind.sample target ∈ ks
  · exact .inr crossed
  · have rowA := good _ (portAt all a)
    have rowB := good _ (portAt all b)
    obtain ⟨outer, own, targetId, exits⟩ := rowB.theta target ends
    have atEnd : outer.Contains b.val := by
      simpa only [pos, Simple.Proofs.number_portAt] using exits
    have atStart : outer.Contains a.val := by
      by_contra outside
      have stay := path.preserves (p := fun v => ¬outer.Contains v.val)
        (fun edge member out inside => by
          rcases (edgeFacts good edge).region outer own inside with h | sampled
          · exact out h
          · exact crossed (targetId ▸ sampled ▸ member)) outside
      exact stay atEnd
    have atA : outer.Contains (pos (portAt all a)) := by
      simpa only [pos, Simple.Proofs.number_portAt] using atStart
    obtain ⟨inner, innerMem, startId, surrounds⟩ := rowA.origin start starts
    rcases surrounds outer own atA with same | inside
    · left
      have equal := targetId.symm.trans same
      rw [equal]
      exact ⟨[], .nil _⟩
    · left
      have proper := actualAncestry code roots own innerMem (startId.symm ▸ inside)
      rw [targetId, startId] at proper
      obtain ⟨ks, walk, _⟩ := proper
      exact ⟨ks, walk⟩

private theorem occursOnWalk {V K : Type} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (walk : Walk e a ks b) {k : K} (inWalk : k ∈ ks) :
    ∃ x y, e x k y := by
  induction walk with
  | nil => cases inWalk
  | cons edge _ ih =>
    rcases List.mem_cons.mp inWalk with rfl | tail
    · exact ⟨_, _, edge⟩
    · exact ih tail

private theorem acrossCut {V K : Type} {e : V → K → V → Prop}
    {a b : V} {ks : List K} (path : Walk e a ks b) {k : K} (inWalk : k ∈ ks)
    (inside : V → Prop)
    (outward : ∀ x y, e x k y → inside x ∧ ¬inside y)
    (noReturn : ∀ {x y k}, e x k y → k ∈ ks → ¬inside x → ¬inside y) :
    inside a ∧ ¬inside b := by
  classical
  induction path with
  | nil => cases inWalk
  | @cons a b c head ks step tail ih =>
    have afterStep : ∀ {x y k}, e x k y → k ∈ ks → ¬inside x → ¬inside y :=
      fun edge mem => noReturn edge (List.mem_cons_of_mem _ mem)
    rcases List.mem_cons.mp inWalk with rfl | later
    · obtain ⟨here, there⟩ := outward a b step
      exact ⟨here, tail.preserves (fun edge mem => afterStep edge mem) there⟩
    · obtain ⟨there, finished⟩ := ih later afterStep
      exact ⟨by by_contra absent; exact noReturn step (.head _) absent there, finished⟩

private theorem crossingBack {V K : Type} {e : V → K → V → Prop}
    {a : V} {ks : List K} (cycle : Walk e a ks a) {k : K} (inWalk : k ∈ ks)
    (inside : V → Prop) (outward : ∀ x y, e x k y → inside x ∧ ¬inside y) :
    ∃ x y eRole, e x eRole y ∧ eRole ∈ ks ∧ ¬inside x ∧ inside y := by
  classical
  by_contra missing
  have keep : ∀ {x y k}, e x k y → k ∈ ks → ¬inside x → ¬inside y :=
    fun step mem outside enters => missing ⟨_, _, _, step, mem, outside, enters⟩
  have impossible := acrossCut cycle inWalk inside outward keep
  exact impossible.2 impossible.1

private theorem structuralOuterFeedback
    (good : GoodRows (regions code (fun r => r) 0 none) (fun r => r)
      (code.rows (fun r => nomatch r) (fun r => r) none)) :
    (code.toGraph roots).OuterFeedbackCycles := by
  intro a ks cycle k mem l observer
  obtain ⟨x, y, witness⟩ := occursOnWalk cycle mem
  obtain ⟨inner, innerMem, innerId⟩ := (edgeFacts good witness).observer l observer
  obtain ⟨cut, lo, hi, forward⟩ : ∃ c : Nat, l.val ≤ c ∧ c ≤ l.val + 1 ∧
      ∀ x y, (code.toGraph roots).Edge x k y → x.val < c ∧ ¬y.val < c := by
    rcases observer with rfl | rfl
    · refine ⟨l.val + 1, by omega, by omega, fun x y edge => ?_⟩
      have h := edgePosition code roots edge
      change x.val ≤ l.val ∧ l.val < y.val at h
      omega
    · refine ⟨l.val, by omega, by omega, fun x y edge => ?_⟩
      have h := edgePosition code roots edge
      have dest := (edgeFacts good edge).index l rfl
      change x.val < y.val at h
      omega
  obtain ⟨u, v, changed, back, member, leaves, enters⟩ :=
    crossingBack cycle mem (fun x => x.val < cut) forward
  have positions := edgePosition code roots back
  cases changed with
  | ordinary | initial | index =>
    change u.val < v.val at positions
    omega
  | sample loop =>
    change u.val ≤ loop.val ∧ loop.val < v.val at positions
    omega
  | feedback loop =>
    obtain ⟨outer, outerMem, outerId, atSource⟩ := (edgeFacts good back).feedback loop rfl
    change loop.val < u.val ∧ loop.val < v.val at positions
    have contains : outer.Contains inner.pass.val := by
      rw [innerId]
      refine ⟨?_, ?_⟩
      · rw [outerId]
        omega
      · have := atSource.2
        omega
    have ancestry := actualAncestry code roots outerMem innerMem contains
    rw [outerId, innerId] at ancestry
    exact ⟨loop, ancestry, member⟩

theorem structuralWellFormed (p : Program P true params t) (neg : P [.bool] .bool) :
    (translate p neg).WellFormed :=
  ⟨forestWellFormed (program p neg).code (program p neg).refs,
    feedbackCycles (program p neg).code (program p neg).refs,
    structuralScope (programGood p neg),
    structuralOuterFeedback (programGood p neg)⟩

end Silmaril.SSA.PEG.Simple.Structured.Proofs
