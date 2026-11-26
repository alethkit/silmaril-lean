module

public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Rows

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars inside all right left : List (Ty Data)} {t : Ty Data}

@[expose] def pos (r : Port all t) : Nat := (numberPort r).id.val

theorem posTail {s : Ty Data} (r : Port all t) :
    pos (Port.tail (s := s) r) = pos r + 1 := rfl

theorem posLeft (r : Port left t) : pos (portLeft (right := right) r) = pos r := by
  induction r with
  | head => rfl
  | tail r ih =>
    simp only [portLeft, posTail, ih]

theorem posRight (left : List (Ty Data)) (r : Port right t) :
    pos (portRight left r) = left.length + pos r := by
  induction left with
  | nil => exact (Nat.zero_add _).symm
  | cons a rest ih =>
    change pos (portRight rest r) + 1 = rest.length + 1 + pos r
    omega

theorem posInside (vars : List (Ty Data)) (r : Port inside t) :
    pos (insideRef vars r) = vars.length + 2 + pos r := by
  unfold insideRef
  rw [posRight, posTail, posTail]
  omega

theorem posPass (vars : List (Ty Data)) :
    pos (passRef (inside := inside) vars) = vars.length := by
  unfold passRef
  rw [posRight]
  rfl

theorem posNeg (vars : List (Ty Data)) :
    pos (negRef (inside := inside) vars) = vars.length + 1 := by
  unfold negRef
  rw [posRight]
  rfl

@[expose] def straightWidth : {after : List (Ty Data)} → Simple.Code P params before after → Nat
  | _, .empty => 0
  | _, .emit prior _ _ => straightWidth prior + 1

@[expose] def width : {before after : List (Ty Data)} → Code P params before after → Nat
  | _, _, .straight code => straightWidth code
  | _, _, .seq a b => width b + width a
  | _, _, .loop (vars := vars) _ body _ _ _ => vars.length + 2 + width body + vars.length

theorem straightPosition (code : Simple.Code P params before after) (r : Port before t) :
    pos (code.lift r) = straightWidth code + pos r := by
  induction code with
  | empty => exact (Nat.zero_add _).symm
  | emit prior _ _ ih =>
    change pos (prior.lift r) + 1 = straightWidth prior + 1 + pos r
    omega

theorem liftPosition (code : Code P params before after) (r : Port before t) :
    pos (code.lift r) = width code + pos r := by
  induction code with
  | straight code => exact straightPosition code r
  | seq a b ihA ihB =>
    change pos (b.lift (a.lift r)) = width b + width a + pos r
    rw [ihB, ihA, Nat.add_assoc]
  | @loop before vars inside init body guard next neg ih =>
    change pos (insideRef vars (body.lift (portRight vars r))) =
      vars.length + 2 + width body + vars.length + pos r
    rw [posInside, ih, posRight]
    omega

theorem codeShift (code : Code P params before after) :
    ∃ k, ∀ t (r : Port before t), pos (code.lift r) = k + pos r :=
  ⟨width code, fun _ r => liftPosition code r⟩

@[expose] def SafeEdge {n : Nat} (a b : Nat) : EdgeKind (Fin n) → Prop
  | .ordinary | .initial _ | .index _ => a < b
  | .feedback l => l.val < a ∧ l.val < b
  | .sample l => a ≤ l.val ∧ l.val < b

private def SafeAt (r : Row P params all t) (a : Nat) : Prop :=
  (∀ l, r.parent = some l → l.val < a) ∧
    (∀ l, passLoop r.label = some l → l.val = a) ∧
    ∀ slot : Fin r.inputs.length,
      SafeEdge a (pos (r.refs.get (portAt r.inputs slot))) (r.label.kind slot)

private theorem mappedNoPass (label : Label P params (Fin 0) left t) :
    passLoop (label.map (fun op => op) (Fin.elim0 (α := Fin all.length))) = none := by
  cases label with
  | param | op | phi => rfl
  | theta impossible | eval impossible | pass impossible => exact impossible.elim0

private theorem mappedOrdinary (label : Label P params (Fin 0) left t) (slot : Fin left.length) :
    (label.map (fun op => op) (Fin.elim0 (α := Fin all.length))).kind slot = .ordinary := by
  cases label with
  | param | op | phi => rfl
  | theta impossible | eval impossible | pass impossible => exact impossible.elim0

private theorem straightSafe (code : Simple.Code P params before after)
    (holes : Rows P params before all) (embed : Embed after all) (offset : Nat)
    (address : ∀ t (r : Port after t), pos (embed r) = offset + pos r)
    (seed : ∀ t (r : Port before t), SafeAt (holes r) (pos (embed (code.lift r))))
    (t : Ty Data) (r : Port after t) : SafeAt (straightRows holes code embed r) (pos (embed r)) := by
  induction code generalizing offset with
  | empty => exact seed t r
  | emit prior label refs ih =>
    cases r with
    | head =>
      refine ⟨(fun l h => by cases h), ?_, fun slot => ?_⟩
      · intro l eq
        change passLoop (label.map (fun op => op) Fin.elim0) = some l at eq
        rw [mappedNoPass] at eq
        cases eq
      change SafeEdge (pos (embed .head))
        (pos ((refs.map (fun _ r => embed (.tail r))).get (portAt _ slot)))
        ((label.map (fun op => op) Fin.elim0).kind slot)
      rw [Simple.Proofs.get_map, mappedOrdinary]
      change pos (embed .head) < pos (embed (.tail (refs.get (portAt _ slot))))
      rw [address, address, posTail]
      change offset + 0 < _
      omega
    | tail r =>
      apply ih (fun q => embed (.tail q)) (offset + 1)
      · intro t r
        rw [address, posTail]
        omega
      · exact seed

private theorem thetaSafe (body : Code P params (vars ++ before) inside)
    (init : Tuple (Port before) vars) (next : Tuple (Port inside) vars)
    (holes : Rows P params before all) (embed : Embed (vars ++ .count :: .bool :: inside) all)
    (offset : Nat)
    (address : ∀ t (r : Port (vars ++ .count :: .bool :: inside) t), pos (embed r) = offset + pos r)
    (r : Port vars t) :
    SafeAt (loopHoles body init next holes embed (portLeft r))
      (pos (embed (insideRef vars (body.lift (portLeft r))))) := by
  rw [loopHoles_left]
  refine ⟨(fun l h => by cases h), (fun l h => by cases h), fun slot => ?_⟩
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => z.elim0) j) slot
  · change pos (embed (insideRef vars (body.lift (portLeft r)))) <
      pos (embed (insideRef vars (body.lift (portRight vars (init.get r)))))
    obtain ⟨k, h⟩ := codeShift body
    rw [address, address, posInside, posInside, h, h, posLeft, posRight]
    have bound : pos r < vars.length := (numberPort r).id.isLt
    omega
  · change pos (embed (passRef vars)) < pos (embed (insideRef vars (body.lift (portLeft r)))) ∧
      pos (embed (passRef vars)) < pos (embed (insideRef vars (next.get r)))
    rw [address, address, address, posPass, posInside, posInside]
    omega

private theorem tableSafe (code : Code P params before after)
    (holes : Rows P params before all) (embed : Embed after all) (outer : Option (Fin all.length))
    (offset : Nat) (address : ∀ t (r : Port after t), pos (embed r) = offset + pos r)
    (older : ∀ l, outer = some l → l.val < offset)
    (seed : ∀ t (r : Port before t), SafeAt (holes r) (pos (embed (code.lift r))))
    (t : Ty Data) (r : Port after t) :
    SafeAt (code.rows holes embed outer r) (pos (embed r)) := by
  induction code generalizing offset t outer with
  | straight code => exact straightSafe code holes embed offset address seed t r
  | seq a b ihA ihB =>
    obtain ⟨k, shift⟩ := codeShift b
    apply ihB _ embed outer offset address older
    intro t q
    apply ihA _ (fun r => embed (b.lift r)) outer (offset + k)
    · intro t r
      rw [address, shift, Nat.add_assoc]
    · intro l eq
      have := older l eq
      omega
    · exact seed
  | @loop before vars inside init body guard next neg ih =>
    let pass := (numberPort (embed (passRef vars))).id
    let inner : Rows P params inside all := body.rows (loopHoles body init next holes embed)
      (fun r => embed (insideRef vars r)) (some pass)
    change SafeAt (loopRows body guard neg outer embed inner r) (pos (embed r))
    rcases WhileProofs.splitCases vars r with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [loopRows_exit]
      refine ⟨(fun l h => by cases h), (fun l h => by cases h), fun slot => ?_⟩
      have bound : pos r < vars.length := (numberPort r).id.isLt
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => z.elim0) j) slot
      · change pos (embed (portLeft r)) ≤ pos (embed (passRef vars)) ∧
          pos (embed (passRef vars)) < pos (embed (insideRef vars (body.lift (portLeft r))))
        rw [address, address, address, posLeft, posPass, posInside]
        omega
      · change pos (embed (portLeft r)) < pos (embed (passRef vars))
        rw [address, address, posLeft, posPass]
        omega
    · cases r with
      | head =>
        change SafeAt (loopRows body guard neg outer embed inner (passRef vars)) (pos (embed (passRef vars)))
        rw [loopRows_pass]
        constructor
        · intro l eq
          have h := older l eq
          rw [address, posPass]
          omega
        · constructor
          · intro l eq
            have same := Option.some.inj eq
            subst l
            rfl
          intro slot
          refine Fin.cases ?_ (fun j => j.elim0) slot
          change pos (embed (passRef vars)) ≤ pos (embed (passRef vars)) ∧
            pos (embed (passRef vars)) < pos (embed (negRef vars))
          rw [address, address, posPass, posNeg]
          omega
      | tail r =>
        cases r with
        | head =>
          change SafeAt (loopRows body guard neg outer embed inner (negRef vars)) (pos (embed (negRef vars)))
          rw [loopRows_neg]
          refine ⟨(fun l h => by cases h), (fun l h => by cases h), fun slot => ?_⟩
          refine Fin.cases ?_ (fun j => j.elim0) slot
          change pos (embed (negRef vars)) < pos (embed (insideRef vars guard))
          rw [address, address, posNeg, posInside]
          omega
        | tail r =>
          change SafeAt (loopRows body guard neg outer embed inner (insideRef vars r))
            (pos (embed (insideRef vars r)))
          rw [loopRows_inside]
          apply ih _ (fun r => embed (insideRef vars r)) (some pass) (offset + vars.length + 2)
          · intro t r
            rw [address, posInside]
            omega
          · intro l eq
            have same := Option.some.inj eq
            subst l
            change pos (embed (passRef vars)) < _
            rw [address, posPass]
            omega
          · intro t r
            rcases WhileProofs.splitCases vars r with ⟨r, rfl⟩ | ⟨r, rfl⟩
            · exact thetaSafe body init next holes embed offset address r
            · rw [loopHoles_right]
              exact seed t r

private theorem closedSafe (code : Code P params [] all) (i : Fin all.length) :
    SafeAt (code.rows (fun r => nomatch r) (fun r => r) none (portAt all i)) i.val := by
  have safe := tableSafe code (fun r => nomatch r) (fun r => r) none 0
    (fun _ _ => (Nat.zero_add _).symm) (fun _ h => by cases h) (fun _ r => nomatch r)
    _ (portAt all i)
  simpa only [pos, Simple.Proofs.number_portAt] using safe

private theorem finRangeOrdered (n : Nat) :
    (List.finRange n).Pairwise (fun (a b : Fin n) => a.val < b.val) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
    rw [List.finRange_succ, List.pairwise_cons, List.pairwise_map]
    constructor
    · intro b mem
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp mem
      exact Nat.zero_lt_succ _
    · exact ih.imp fun {a b} h => Nat.succ_lt_succ h

private theorem scanRank {n : Nat} (a b pivot : Fin n) (kind : EdgeKind (Fin n))
    (steps : List (Fin n))
    (ordered : steps.Pairwise (fun a b => a.val < b.val)) (mem : pivot ∈ steps)
    (before : ∀ j : Fin n, j.val < pivot.val →
      (RankComponent.phase (fun (i : Fin n) => if i.val ≤ j.val then 1 else 0)).change a b kind = .equal ∧
      (RankComponent.counter j).change a b kind = .equal)
    (atPivot :
      let p := (RankComponent.phase (fun (i : Fin n) => if i.val ≤ pivot.val then 1 else 0)).change a b kind
      p = .lower ∨ (p = .equal ∧ (RankComponent.counter pivot).change a b kind = .lower)) :
    DemandRank.checkEdge (steps.flatMap (fun j =>
      [.phase (fun i => if i.val ≤ j.val then 1 else 0), .counter j])) a b kind = true := by
  induction steps with
  | nil => cases mem
  | cons j steps ih =>
    rcases List.mem_cons.mp mem with rfl | tail
    · rcases atPivot with h | ⟨h, tick⟩
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append, DemandRank.checkEdge, h]
      · simp only [List.flatMap_cons, List.cons_append, List.nil_append, DemandRank.checkEdge, h, tick]
    · obtain ⟨first, rest⟩ := List.pairwise_cons.mp ordered
      obtain ⟨phase, count⟩ := before j (first pivot tail)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, DemandRank.checkEdge, phase, count]
      exact ih rest tail

private theorem rankEdge {n : Nat} (a b : Fin n) (kind : EdgeKind (Fin n))
    (h : SafeEdge a.val b.val kind) : (rank n).checkEdge a b kind = true := by
  have plain (step : a.val < b.val)
      (counterEq : ∀ j : Fin n, j.val < a.val → (RankComponent.counter j).change a b kind = .equal) :
      (rank n).checkEdge a b kind = true := by
    apply scanRank a b a kind _ (finRangeOrdered n) (List.mem_finRange a)
    · intro j lt
      refine ⟨?_, counterEq j lt⟩
      have afterB : ¬b.val ≤ j.val := by omega
      simp [RankComponent.change, Nat.not_le_of_lt lt, afterB]
    · have afterB : ¬b.val ≤ a.val := by omega
      exact .inl (by simp [RankComponent.change, afterB])
  cases kind with
  | ordinary | initial | index => exact plain h (fun _ _ => rfl)
  | sample l =>
    obtain ⟨al, lb⟩ := h
    apply plain (by omega)
    intro j lt
    have distinct : j ≠ l := fun eq => by subst j; omega
    simp [RankComponent.change, distinct]
  | feedback l =>
    obtain ⟨la, lb⟩ := h
    apply scanRank a b l (.feedback l) _ (finRangeOrdered n) (List.mem_finRange l)
    · intro j lt
      have aj : ¬a.val ≤ j.val := by omega
      have bj : ¬b.val ≤ j.val := by omega
      have distinct : j ≠ l := fun eq => by subst j; omega
      simp [RankComponent.change, aj, bj, distinct]
    · exact .inr ⟨by simp [RankComponent.change, Nat.not_le_of_lt la, Nat.not_le_of_lt lb], by
        simp [RankComponent.change]⟩

theorem edgePosition (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) {a b : Fin all.length} {kind : EdgeKind (Fin all.length)}
    (edge : (code.toGraph roots).Edge a kind b) : SafeEdge a.val b.val kind := by
  obtain ⟨slot, rfl, rfl⟩ := edge
  let r : Row P params all all[a] := code.rows (fun r => nomatch r) (fun r => r) none (portAt all a)
  change SafeEdge a.val (((r.refs.map (fun _ r => numberPort r)).get (portAt r.inputs slot)).id.val)
    (r.label.kind slot)
  rw [Simple.Proofs.get_map]
  exact (closedSafe code a).2.2 slot

theorem rankChecked (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) : (rank all.length).check (code.toGraph roots) = true := by
  unfold DemandRank.check
  apply List.all_eq_true.mpr
  intro a _
  apply List.all_eq_true.mpr
  intro slot _
  let row : Row P params all all[a] := code.rows (fun r => nomatch r) (fun r => r) none (portAt all a)
  change (rank all.length).checkEdge a ((row.refs.map (fun _ r => numberPort r)).get
    (portAt row.inputs slot)).id (row.label.kind slot) = true
  rw [Simple.Proofs.get_map]
  exact rankEdge _ _ _ ((closedSafe code a).2.2 slot)

theorem passAtOwnId (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) (row l : Fin all.length)
    (h : passLoop ((code.toGraph roots).node row).label = some l) : l = row :=
  Fin.ext ((closedSafe code row).2.1 l h)

theorem feedbackCycles (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) : (code.toGraph roots).FeedbackCycles := by
  intro i ks walk nonempty
  by_contra noFeedback
  have drop := walk.strictRank nonempty (fun j => all.length - j.val)
    (fun {a b k} edge member => by
      obtain ⟨slot, rfl, rfl⟩ := edge
      let r : Row P params all all[a] := code.rows (fun r => nomatch r) (fun r => r) none (portAt all a)
      have safe := (closedSafe code a).2.2 slot
      change SafeEdge a.val (pos (r.refs.get (portAt r.inputs slot))) (r.label.kind slot) at safe
      have bound := (numberPort (r.refs.get (portAt r.inputs slot))).id.isLt
      have forward : a.val < pos (r.refs.get (portAt r.inputs slot)) := by
        change r.label.kind slot ∈ ks at member
        cases h : r.label.kind slot with
        | ordinary | initial | index =>
          rw [h] at safe
          exact safe
        | sample l =>
          rw [h] at safe
          exact Nat.lt_of_le_of_lt safe.1 safe.2
        | feedback l =>
          rw [h] at member
          exact (noFeedback ⟨_, member, trivial⟩).elim
      change all.length - (((r.refs.map (fun _ r => numberPort r)).get (portAt r.inputs slot)).id.val) <
        all.length - a.val
      rw [Simple.Proofs.get_map]
      change all.length - pos (r.refs.get (portAt r.inputs slot)) < all.length - a.val
      change pos (r.refs.get (portAt r.inputs slot)) < all.length at bound
      omega)
  exact Nat.lt_irrefl _ drop

theorem earlierParent (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) (child parent : Fin all.length)
    (h : (code.toGraph roots).forest.parent child = some parent) : parent.val < child.val :=
  (closedSafe code child).1 parent h

theorem forestWellFormed (code : Code P params [] all) {outs : List (Ty Data)}
    (roots : Tuple (Port all) outs) : (code.toGraph roots).forest.WellFormed := by
  rintro i ⟨ks, walk, nonempty⟩
  have decrease := walk.strictRank nonempty Fin.val fun h _ => earlierParent code roots _ _ h
  exact (Nat.lt_irrefl _ decrease)

end Silmaril.SSA.PEG.Simple.Structured.Proofs
