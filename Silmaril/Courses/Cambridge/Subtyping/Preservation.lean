module

public import Silmaril.Courses.Cambridge.Subtyping.Progress
public import Silmaril.Courses.Cambridge.Subtyping.Substitution

/-! # Preservation and safety for L3 with subsumption -/

public section

namespace Silmaril.Courses.Cambridge.Subtyping

open L3 (Loc Ty Expr Store Value Config LocTypes VarTypes RecordLabels Step Steps)

private theorem StoreTyped.insert {Θ : LocTypes} {s : Store} {address : Loc}
    {value : Value} {T : Ty} (store : StoreTyped Θ s)
    (typed : HasType Θ .empty value.val T)
    (extension : Θ.Extends (Θ.insert address T)) :
    StoreTyped (Θ.insert address T) (s.insert address value) where
  domain loc := by simp [store.domain loc]
  contents := by
    intro loc U v typeLookup valueLookup
    by_cases same : loc = address
    · subst loc
      have typeEq : T = U := Option.some.inj (by simpa only [Finmap.lookup_insert] using typeLookup)
      have valueEq : value = v := Option.some.inj (by simpa only [Finmap.lookup_insert] using valueLookup)
      cases typeEq
      cases valueEq
      exact typed.weakenLocs extension
    · rw [Finmap.lookup_insert_of_ne _ same] at typeLookup valueLookup
      exact (store.contents typeLookup valueLookup).weakenLocs extension

private theorem LocTypes.extends_insert {Θ : LocTypes} {address : Loc} {T : Ty}
    (fresh : address ∉ Θ) : Θ.Extends (Θ.insert address T) := by
  intro loc U lookup
  have different : loc ≠ address := fun same => fresh (same ▸ Finmap.mem_of_lookup_eq_some lookup)
  simpa only [Finmap.lookup_insert_of_ne _ different] using lookup

private theorem StoreTyped.assign {Θ : LocTypes} {s : Store} {address : Loc}
    {value : Value} {T : Ty} (store : StoreTyped Θ s)
    (typed : HasType Θ .empty value.val T) (lookup : Θ.lookup address = some T) :
    StoreTyped Θ (s.insert address value) := by
  have same : Θ.insert address T = Θ := by
    apply Finmap.ext_lookup
    intro loc
    by_cases equal : loc = address
    · subst loc
      simp [lookup]
    · simp [equal]
  have extension : Θ.Extends (Θ.insert address T) := by
    rw [same]
    exact LocTypes.Extends.refl Θ
  simpa only [same] using store.insert typed extension

private theorem loc_lookup {Θ : LocTypes} {Γ : VarTypes} {loc : Loc} {T : Ty}
    (typed : HasType Θ Γ (.loc loc) (.ref T)) : Θ.lookup loc = some T := by
  obtain ⟨_, head, sub⟩ := typed.valueTyping (.loc loc)
  cases Subty.reference_inv sub rfl
  cases head
  assumption

private theorem preserve {Θ : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) :
    ∀ {s : Store} {after : Config}, Γ = .empty →
      Step ⟨e, s⟩ after → StoreTyped Θ s →
      ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' Γ after.expr T ∧ StoreTyped Θ' after.store := by
  induction typed <;> intro s after closed step store
  case sub _ sub ih =>
    obtain ⟨Θ', extension, typed', store'⟩ := ih closed step store
    exact ⟨Θ', extension, .sub typed' sub, store'⟩
  case int => cases step
  case bool => cases step
  case skip => cases step
  case bvar => cases step
  case fvar => cases step
  case lam => cases step
  case loc => cases step
  case add hl hr ihl ihr =>
    cases step with
    | add => exact ⟨Θ, LocTypes.Extends.refl Θ, .int _, store⟩
    | binaryLeft step =>
      obtain ⟨Θ', extension, left, store'⟩ := ihl closed step store
      exact ⟨Θ', extension, .add left (hr.weakenLocs extension), store'⟩
    | binaryRight _ step =>
      obtain ⟨Θ', extension, right, store'⟩ := ihr closed step store
      exact ⟨Θ', extension, .add (hl.weakenLocs extension) right, store'⟩
  case ge hl hr ihl ihr =>
    cases step with
    | ge => exact ⟨Θ, LocTypes.Extends.refl Θ, .bool _, store⟩
    | binaryLeft step =>
      obtain ⟨Θ', extension, left, store'⟩ := ihl closed step store
      exact ⟨Θ', extension, .ge left (hr.weakenLocs extension), store'⟩
    | binaryRight _ step =>
      obtain ⟨Θ', extension, right, store'⟩ := ihr closed step store
      exact ⟨Θ', extension, .ge (hl.weakenLocs extension) right, store'⟩
  case cond ht hy hn iht _ _ =>
    cases step with
    | ifTrue => exact ⟨Θ, LocTypes.Extends.refl Θ, hy, store⟩
    | ifFalse => exact ⟨Θ, LocTypes.Extends.refl Θ, hn, store⟩
    | ifStep step =>
      obtain ⟨Θ', extension, test, store'⟩ := iht closed step store
      exact ⟨Θ', extension, .cond test (hy.weakenLocs extension) (hn.weakenLocs extension), store'⟩
  case seq _ hr ihl _ =>
    cases step with
    | seqSkip => exact ⟨Θ, LocTypes.Extends.refl Θ, hr, store⟩
    | seqStep step =>
      obtain ⟨Θ', extension, left, store'⟩ := ihl closed step store
      exact ⟨Θ', extension, .seq left (hr.weakenLocs extension), store'⟩
  case loop ht hb _ _ =>
    cases step
    exact ⟨Θ, LocTypes.Extends.refl Θ, .cond ht (.seq hb (.loop ht hb)) .skip, store⟩
  case app hf ha ihf iha =>
    cases step with
    | appLeft step =>
      obtain ⟨Θ', extension, fn, store'⟩ := ihf closed step store
      exact ⟨Θ', extension, .app fn (ha.weakenLocs extension), store'⟩
    | appRight _ step =>
      obtain ⟨Θ', extension, arg, store'⟩ := iha closed step store
      exact ⟨Θ', extension, .app (hf.weakenLocs extension) arg, store'⟩
    | appFun =>
      obtain ⟨_, head, sub⟩ := hf.valueTyping (.lam _ _)
      obtain ⟨_, _, rfl, domain, result⟩ := L3Subty.arr_inv sub
      cases head with
      | lam hb => exact ⟨Θ, LocTypes.Extends.refl Θ, .sub (hb.beta (.sub ha domain)) result, store⟩
  case letE hv hb ihv _ =>
    cases step with
    | letStep step =>
      obtain ⟨Θ', extension, value, store'⟩ := ihv closed step store
      exact ⟨Θ', extension, .letE value (hb.weakenLocs extension), store'⟩
    | letValue => exact ⟨Θ, LocTypes.Extends.refl Θ, hb.beta hv, store⟩
  case letRecFun hf hb _ _ =>
    cases step
    exact ⟨Θ, LocTypes.Extends.refl Θ, hb.beta hf.recClosure, store⟩
  case pair hl hr ihl ihr =>
    cases step with
    | pairLeft step =>
      obtain ⟨Θ', extension, left, store'⟩ := ihl closed step store
      exact ⟨Θ', extension, .pair left (hr.weakenLocs extension), store'⟩
    | pairRight _ step =>
      obtain ⟨Θ', extension, right, store'⟩ := ihr closed step store
      exact ⟨Θ', extension, .pair (hl.weakenLocs extension) right, store'⟩
  case fst hp ih =>
    cases step with
    | fstStep step =>
      obtain ⟨Θ', extension, pair, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .fst pair, store'⟩
    | fstValue vl vr =>
      obtain ⟨_, head, sub⟩ := hp.valueTyping (.pair vl vr)
      obtain ⟨_, _, rfl, left, _⟩ := L3Subty.prod_inv sub
      cases head with
      | pair hl _ => exact ⟨Θ, LocTypes.Extends.refl Θ, .sub hl left, store⟩
  case snd hp ih =>
    cases step with
    | sndStep step =>
      obtain ⟨Θ', extension, pair, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .snd pair, store'⟩
    | sndValue vl vr =>
      obtain ⟨_, head, sub⟩ := hp.valueTyping (.pair vl vr)
      obtain ⟨_, _, rfl, _, right⟩ := L3Subty.prod_inv sub
      cases head with
      | pair _ hr => exact ⟨Θ, LocTypes.Extends.refl Θ, .sub hr right, store⟩
  case inl _ ih =>
    cases step with
    | inl step =>
      obtain ⟨Θ', extension, payload, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .inl payload, store'⟩
  case inr _ ih =>
    cases step with
    | inr step =>
      obtain ⟨Θ', extension, payload, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .inr payload, store'⟩
  case matchSum he hl hr ih _ _ =>
    cases step with
    | matchStep step =>
      obtain ⟨Θ', extension, scrutinee, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .matchSum scrutinee (hl.weakenLocs extension) (hr.weakenLocs extension), store'⟩
    | matchLeft value =>
      obtain ⟨_, head, sub⟩ := he.valueTyping (.inl value)
      obtain ⟨_, _, rfl, left, _⟩ := L3Subty.sum_inv sub
      cases head with
      | inl payload => exact ⟨Θ, LocTypes.Extends.refl Θ, hl.beta (.sub payload left), store⟩
    | matchRight value =>
      obtain ⟨_, head, sub⟩ := he.valueTyping (.inr value)
      obtain ⟨_, _, rfl, _, right⟩ := L3Subty.sum_inv sub
      cases head with
      | inr payload => exact ⟨Θ, LocTypes.Extends.refl Θ, hr.beta (.sub payload right), store⟩
  case record fields ih =>
    cases step with
    | recordStep i _ step =>
      obtain ⟨Θ', extension, updated, store'⟩ := ih i closed step store
      refine ⟨Θ', extension, .record (fun j => ?_), store'⟩
      by_cases same : j = i
      · subst j
        simpa only [Function.update_self] using updated
      · simpa only [Function.update_of_ne same] using (fields j).weakenLocs extension
  case project i he ih =>
    generalize name : RecordLabels.label _ i = label at step
    cases step with
    | projectStep step =>
      obtain ⟨Θ', extension, record, store'⟩ := ih closed step store
      rw [← name]
      exact ⟨Θ', extension, .project i record, store'⟩
    | projectValue j ready =>
      obtain ⟨_, head, sub⟩ := he.valueTyping (.record ready)
      obtain ⟨_, _, rfl, fields⟩ := L3Subty.record_inv sub
      obtain ⟨k, selected, fieldSub⟩ := fields i
      cases head with
      | record types =>
        have same : k = j := RecordLabels.eq_of_label_eq (selected.trans name)
        cases same
        exact ⟨Θ, LocTypes.Extends.refl Θ, .sub (types _) fieldSub, store⟩
  case ref _ _ contents hv ih =>
    cases step with
    | refStep step =>
      obtain ⟨Θ', extension, value, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .ref value, store'⟩
    | refValue value fresh =>
      cases closed
      have extension : Θ.Extends (Θ.insert _ contents) :=
        LocTypes.extends_insert (fun present => fresh ((store.domain _).mp present))
      exact ⟨_, extension, .loc (Finmap.lookup_insert Θ), store.insert hv extension⟩
  case deref he ih =>
    cases step with
    | derefStep step =>
      obtain ⟨Θ', extension, ref, store'⟩ := ih closed step store
      exact ⟨Θ', extension, .deref ref, store'⟩
    | derefValue present =>
      cases closed
      exact ⟨Θ, LocTypes.Extends.refl Θ, store.contents (loc_lookup he) present, store⟩
  case assign hl hr ihl ihr =>
    cases step with
    | assignLeft step =>
      obtain ⟨Θ', extension, lhs, store'⟩ := ihl closed step store
      exact ⟨Θ', extension, .assign lhs (hr.weakenLocs extension), store'⟩
    | assignRight step =>
      obtain ⟨Θ', extension, rhs, store'⟩ := ihr closed step store
      exact ⟨Θ', extension, .assign (hl.weakenLocs extension) rhs, store'⟩
    | assignValue =>
      cases closed
      exact ⟨Θ, LocTypes.Extends.refl Θ, .skip, store.assign hr (loc_lookup hl)⟩

/-- One L3 step preserves the type and store typing, extending the location
environment when a fresh reference is allocated. -/
theorem preservation {Θ : LocTypes} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Θ .empty before.expr T)
    (store : StoreTyped Θ before.store) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty after.expr T ∧ StoreTyped Θ' after.store := by
  obtain ⟨e, s⟩ := before
  exact preserve typed rfl step store

/-- Every configuration reached from a well-typed closed L3 expression and a
well-typed store is a value or can take another L3 step. -/
theorem safety {Θ : LocTypes} {start finish : Config} {T : Ty}
    (steps : Steps start finish) (typed : HasType Θ .empty start.expr T)
    (store : StoreTyped Θ start.store) :
    L3.IsValue finish.expr ∨ ∃ next, Step finish next := by
  have maintained : ∃ Θ', HasType Θ' .empty finish.expr T ∧ StoreTyped Θ' finish.store := by
    induction steps with
    | refl => exact ⟨Θ, typed, store⟩
    | tail _ step ih =>
      obtain ⟨_, typed', store'⟩ := ih
      obtain ⟨Θ', _, typed'', store''⟩ := preservation step typed' store'
      exact ⟨Θ', typed'', store''⟩
  obtain ⟨_, typed', store'⟩ := maintained
  obtain ⟨e, s⟩ := finish
  exact progress typed' store'

end Silmaril.Courses.Cambridge.Subtyping
