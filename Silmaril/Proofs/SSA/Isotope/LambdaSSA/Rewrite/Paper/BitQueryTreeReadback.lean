module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Thms

/-! # Native certificates for the finite Bit request readback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Live slots literalQuery forwarding enter? Candidate Verdict)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

private theorem slots_ext {Γ : List (Ty Empty)} {n : Nat} {a b : Slots Γ n}
    (h : a.index = b.index) : a = b := by
  cases a
  cases b
  cases h
  rfl

private theorem nextSlot (n : Nat) : (slots n).bind = slots (n + 1) :=
  slots_ext (funext fun i => Fin.cases rfl (fun _ => rfl) i)

private theorem labelShift (pre : List (Ty Empty)) :
    Ren Exits (pre ++ Exits) (pre.length + ·) := by
  intro i A hi
  simpa [At, List.getElem?_append_right (Nat.le_add_right _ _)] using hi

private theorem requestType {Γ : List (Ty Empty)} {label : Bool} {arg : Tm signature.Instr}
    {A B : Ty Empty} (ha : Tm.HasType Γ (.op (.ask label) arg) (Ty.coprod A B)) :
    A = Bit ∧ B = Bit := by
  cases ha
  exact ⟨rfl, rfl⟩

private theorem literalQuery_eq {a : Tm signature.Instr} {b : Bool} (h : literalQuery a = some b) :
    a = literal b := by
  fun_cases literalQuery a <;> simp_all [literalQuery, literal, constructorBit]

private theorem dropVar {Γ L : List (Ty Empty)} {i : Nat} {A : Ty Empty} {r : Region signature.Instr}
    (ha : Tm.HasType Γ (.var i : Tm signature.Instr) A) (hr : ValueBranches (A :: Γ) r L) :
    ValueBranches Γ (r.substVars (Tm.singleSubst (.var i))) L ∧
      Paper.Eqv Γ (.let₁ (.var i) r) (r.substVars (Tm.singleSubst (.var i))) L := by
  cases ha with
  | var hi =>
    refine ⟨hr.substVars ?_, .cfgEta (.native (.letValue (.var hi) hr.hasType))⟩
    intro j B hj
    cases j with
    | zero =>
      have e : A = B := Option.some.inj hj
      subst B
      exact .var hi
    | succ j => exact .var hj

private theorem enterBranch {Γ L : List (Ty Empty)} {k i j : Nat} (hi : i < k + 1)
    {rows : Fin (k + 1) → Region signature.Instr}
    (ht : ValueBranches Γ (.cfg (.br i (.var j)) (k + 1) rows) L) :
    let target := .cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) (k + 1) rows
    ValueBranches Γ target L ∧ Paper.Eqv Γ (.cfg (.br i (.var j)) (k + 1) rows) target L := by
  cases ht with
  | cfg R entry hb =>
    cases entry with
    | br atLabel hv =>
      have hR : At (List.ofFn R ++ L) i (R ⟨i, hi⟩) := by
        have bound : i < (List.ofFn R).length := by simpa using hi
        simp only [At, List.getElem?_append_left bound, List.getElem?_ofFn, hi, dite_true]
      cases Option.some.inj (atLabel.symm.trans hR)
      have ⟨targetTyped, beta⟩ := dropVar hv.hasType (hb ⟨i, hi⟩)
      have step := Paper.Eqv.cfgEta (.native (.base (.entry
        (.cfgBrLocal R ⟨i, hi⟩ hv (fun j => (hb j).hasType)))))
      exact ⟨.cfg R targetTyped hb, step.trans (.cfg R beta (fun j => .refl (hb j).hasType))⟩

private theorem enterOne {Γ L : List (Ty Empty)} {e : Region signature.Instr}
    {rows : Fin 1 → Region signature.Instr}
    (ht : ValueBranches Γ (.cfg e 1 rows) L) :
    ValueBranches Γ (e.lsubst (cfgEntryContinuations rows)) L ∧
      Paper.Eqv Γ (.cfg e 1 rows) (e.lsubst (cfgEntryContinuations rows)) L := by
  cases ht with
  | cfg R he hb =>
    have family : LSubst.ValueFamily Γ (List.ofFn R ++ L) L (cfgEntryContinuations rows) :=
      fun _ A h => .cfg R (.br h (.var rfl))
        (fun i => (hb i).renameVars ((Ren.wk Γ A).lift (R i)))
    have constant : (fun _ : Fin 1 => rows 0) = rows :=
      funext fun i => congrArg rows (Subsingleton.elim _ _)
    have entry : ValueBranches Γ e (R 0 :: L) := by simpa using he
    have block : ValueBranches (R 0 :: Γ) (rows 0) (R 0 :: L) := by simpa using hb 0
    have eq := CfgEta.Eqv.eta entry block
    unfold CfgEta.singleCfg CfgEta.reentry at eq
    rw [constant] at eq
    exact ⟨he.lsubst family, .cfgEta eq⟩

private theorem enter_sound {Γ L : List (Ty Empty)} {k : Nat} {e r : Region signature.Instr}
    {rows : Fin k → Region signature.Instr} (ht : ValueBranches Γ (.cfg e k rows) L)
    (h : enter? k e rows = some r) :
    ValueBranches Γ r L ∧ Paper.Eqv Γ (.cfg e k rows) r L := by
  cases found : forwarding e with
  | none =>
    by_cases hk : k = 1
    · subst k
      have target : some (e.lsubst (cfgEntryContinuations rows)) = some r := by
        simpa [enter?, found] using h
      cases Option.some.inj target
      exact enterOne ht
    · simp [enter?, found, hk] at h
  | some dest =>
    obtain ⟨i, j⟩ := dest
    have source : e = .br i (.var j) := by
      fun_cases forwarding e <;> simp_all [forwarding]
    subst e
    by_cases hi : i < k
    · have target : some (.cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) k rows) =
          some r := by
        simpa only [enter?, forwarding, hi, dite_true] using h
      cases Option.some.inj target
      cases k with
      | zero => omega
      | succ k => exact enterBranch hi ht
    · simp [enter?, forwarding, hi] at h

private theorem leave {Γ L : List (Ty Empty)} {k : Nat} (R : Fin k → Ty Empty)
    {e r : Region signature.Instr} {rows : Fin k → Region signature.Instr}
    (hb : ∀ i, ValueBranches (R i :: Γ) (rows i) (List.ofFn R ++ L))
    (hr : HasType Γ r L)
    (eq : Paper.Eqv Γ e (r.renameLabels (k + ·)) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg e k rows) r L := by
  refine (.cfg R eq (fun j => .refl (hb j).hasType) : Paper.Eqv _ _ _ _).trans ?_
  refine .cfgEta (.native ?_)
  cases k with
  | zero =>
    simpa only [Nat.zero_add, show (fun j : Nat => j) = id from rfl, renameLabels_id] using
      SubstitutionEquiv.base (.entry (.cfgZero hr rows))
  | succ k => exact .cfgOutward R hr (fun i => (hb i).hasType)

theorem read_sound (fuel n : Nat) (pre : List (Ty Empty)) {r : Region signature.Instr} {t : Tree n}
    (hr : ValueBranches (Live n) r (pre ++ Exits)) (h : Readback.read fuel n pre.length r = some t) :
    Paper.Eqv (Live n) r ((t.region (slots n)).renameLabels (pre.length + ·)) (pre ++ Exits) := by
  induction fuel generalizing n pre r with
  | zero => cases h
  | succ fuel ih =>
    cases r with
    | br i a =>
      cases a
      case var j =>
        simp only [Readback.read] at h
        split at h
        · rename_i within
          change (if i = pre.length then some (.ret false ⟨j, within⟩)
            else if i = pre.length + 1 then some (.ret true ⟨j, within⟩) else none) = some t at h
          split at h
          · rename_i atExit
            cases h
            simpa [Tree.region, Slots.terms, slots, renameLabels, atExit] using Paper.Eqv.refl hr.hasType
          · split at h
            · rename_i atExit
              cases h
              simpa [Tree.region, Slots.terms, slots, renameLabels, atExit] using Paper.Eqv.refl hr.hasType
            · cases h
        · cases h
      all_goals simp [Readback.read] at h
    | case a left right =>
      cases a
      case op f a =>
        cases f with
        | ask label =>
          simp only [Readback.read] at h
          obtain ⟨query, hquery, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨r, hright, h⟩ := Option.bind_eq_some_iff.mp h
          cases h
          cases hr with
          | case ha hleft hrightTyped =>
            obtain ⟨rfl, rfl⟩ := requestType ha
            have ea := literalQuery_eq hquery
            subst a
            cases query <;>
              simpa only [Tree.region, choose, requestRegion, renameLabels, nextSlot, Bool.false_eq_true, ite_false, ite_true] using
                Paper.Eqv.case ha (ih (n + 1) pre hleft hl) (ih (n + 1) pre hrightTyped hright)
      all_goals simp [Readback.read] at h
    | let₁ a body =>
      cases a
      case var j =>
        simp only [Readback.read] at h
        cases hr with
        | let₁ ha hbody =>
          obtain ⟨typed, eq⟩ := dropVar ha hbody
          exact eq.trans (ih n pre typed h)
      all_goals simp [Readback.read] at h
    | let₂ a body => simp [Readback.read] at h
    | cfg entry k rows =>
      simp only [Readback.read] at h
      cases found : Readback.read fuel n (k + pre.length) entry with
      | none =>
        rw [found] at h
        obtain ⟨r, outward, rest⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨typed, eq⟩ := enter_sound hr outward
        exact eq.trans (ih n pre typed rest)
      | some tt =>
        rw [found] at h
        cases h
        cases hr with
        | cfg R he hb =>
          have found' : Readback.read fuel n (List.ofFn R ++ pre).length entry = some t := by
            simpa only [List.length_append, List.length_ofFn] using found
          have he' : ValueBranches (Live n) entry ((List.ofFn R ++ pre) ++ Exits) := by
            simpa only [List.append_assoc] using he
          have eq := ih n (List.ofFn R ++ pre) he' found'
          simp only [List.append_assoc, List.length_append, List.length_ofFn] at eq
          rw [← show (k + ·) ∘ (pre.length + ·) = (k + pre.length + ·) from
            funext fun j => (Nat.add_assoc k pre.length j).symm, ← renameLabels_comp] at eq
          exact leave R hb ((t.typed (slots n)).hasType.renameLabels (labelShift pre)) eq

private theorem firstSlots : slots 1 = inputSlots :=
  slots_ext (funext fun i => congrArg Fin.val (Subsingleton.elim i (0 : Fin 1)))

theorem packed_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) : p.packed = t.defaultPacked := by
  have step := read_sound fuel 1 [] p.property h
  simp only [List.length_nil, Nat.zero_add, show (fun j : Nat => j) = id from rfl,
    renameLabels_id, firstSlots] at step
  have eq := Paper.Eqv.lsubstPost step p.property (t.typed inputSlots)
    (fun _ _ hj => (packExits_valueFamily (Φ := signature.Instr) [Bit] Exits hj).hasType)
  exact (Paper.TypeCategory.ofRegion_eq_iff p.property.packExits t.guarded_typed.packExits).mpr
    (eq.trans (.cfgEta (.native (native_packed_unguarded t).symm)))

theorem observations_eq {fuel : Nat} {p : Candidate} {t : Tree 1}
    (h : p.read fuel = some t) (guard : Bool) : p.observations guard = t.observations guard := by
  unfold Candidate.observations
  rw [packed_eq h]
  rfl

theorem eq_iff_key {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ t.key = u.key := by
  rw [packed_eq hp, packed_eq hq]
  exact default_eq_iff_key t u

theorem compare_equal {fuel : Nat} {p q : Candidate} (h : Readback.compare fuel p q = .equal) :
    p.packed = q.packed := by
  unfold Readback.compare at h
  split at h
  · rename_i t u hp hq
    split at h
    · rename_i absent
      exact (packed_eq hp).trans (((separate_none_iff_default t u).mp absent).trans (packed_eq hq).symm)
    · cases h
  · cases h

theorem compare_different {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  unfold Readback.compare at h
  split at h
  · rename_i t u hp hq
    split at h
    · cases h
    · rename_i w' found
      cases h
      have unequal : t.defaultPacked ≠ u.defaultPacked := by
        intro eq
        rw [(separate_none_iff_default t u).2 eq] at found
        cases found
      obtain ⟨v, hv, hsrc, htgt⟩ := separate_of_default_ne t u unequal
      have sameWitness : v = w := Option.some.inj (hv.symm.trans found)
      subst v
      cases side : w.fromRight
      · change w.history.observation ∈ p.observations w.guard ∧
          w.history.observation ∉ q.observations w.guard
        rw [observations_eq hp, observations_eq hq]
        simp only [Difference.source, Difference.target, side, Bool.false_eq_true, ite_false] at hsrc htgt
        exact ⟨hsrc, htgt⟩
      · change w.history.observation ∈ q.observations w.guard ∧
          w.history.observation ∉ p.observations w.guard
        rw [observations_eq hp, observations_eq hq]
        simp only [Difference.source, Difference.target, side, ite_true] at hsrc htgt
        exact ⟨hsrc, htgt⟩
  · cases h

theorem compare_equal_iff {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    Readback.compare fuel p q = .equal ↔ p.packed = q.packed := by
  constructor
  · exact compare_equal
  · intro eq
    rw [packed_eq hp, packed_eq hq] at eq
    simp only [Readback.compare, hp, hq, (separate_none_iff_default t u).2 eq]

theorem eq_iff_observations {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) :
    p.packed = q.packed ↔ ∀ guard, p.observations guard = q.observations guard := by
  rw [packed_eq hp, packed_eq hq]
  simp only [observations_eq hp, observations_eq hq]
  exact default_eq_iff_observations t u

theorem compare_different_ne {fuel : Nat} {p q : Candidate} {w : Difference}
    (h : Readback.compare fuel p q = .different w) : p.packed ≠ q.packed := by
  obtain ⟨inLeft, notInRight⟩ := compare_different h
  intro eq
  have same : p.observations w.guard = q.observations w.guard := by
    unfold Candidate.observations
    rw [eq]
  cases side : w.fromRight <;> simp_all

theorem compare_diff_of_ne {fuel : Nat} {p q : Candidate} {t u : Tree 1}
    (hp : p.read fuel = some t) (hq : q.read fuel = some u) (hne : p.packed ≠ q.packed) :
    ∃ w, Readback.compare fuel p q = .different w := by
  have unequal : t.defaultPacked ≠ u.defaultPacked :=
    fun h => hne ((packed_eq hp).trans (h.trans (packed_eq hq).symm))
  obtain ⟨w, hw, _, _⟩ := separate_of_default_ne t u unequal
  exact ⟨w, by simp only [Readback.compare, hp, hq, hw]⟩

namespace Example

open Readback.Example

private theorem joined_typed (right : Bool) (pre Γ : List (Ty Empty)) :
    ValueBranches Γ (joined right pre.length) (pre ++ Exits) := by
  refine .cfg (fun _ => Bit) (.case (.op (constructorBit_value false .unit).hasType)
    (.br rfl (.var (i := 0) rfl)) (.br rfl (.var (i := 0) rfl))) (fun _ => ?_)
  have atExit := labelShift (Bit :: pre) (exit_typed right)
  exact .br (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using atExit)
    (.var (i := 0) rfl)

theorem forward_typed (right : Bool) : ValueBranches [Bit] (forward right) Exits := by
  refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
  refine Fin.cases (.br rfl (.var (i := 0) rfl)) (fun _ => ?_)
  exact joined_typed right [Bit, Bit] [Bit, Bit]

theorem backward_typed (right : Bool) : ValueBranches [Bit] (backward right) Exits := by
  refine .cfg (fun _ => Bit) (.br rfl (.var (i := 0) rfl)) ?_
  refine Fin.cases ?_ (fun _ => .br rfl (.var (i := 0) rfl))
  exact joined_typed right [Bit, Bit] [Bit, Bit]

end Example

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeReadback
