module

public import Silmaril.Courses.Cambridge.L3.Metatheory.Substitution
public import Silmaril.Courses.Cambridge.L3.Metatheory.Progress

/-! # Cambridge L3 preservation and safety (Theorems 24–25, p. 75) -/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3

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

private theorem record_projection_type {Θ : LocTypes} {labels : RecordLabels}
    {fields : labels.Index → Expr} {label : Label} {i : labels.Index} {T : Ty}
    (typed : HasType Θ .empty (.project (.record labels fields) label) T)
    (selected : labels.label i = label) : HasType Θ .empty (fields i) T := by
  cases typed with
  | project j typed =>
      cases typed with
      | record fieldTypes =>
          have same : i = j := RecordLabels.eq_of_label_eq selected
          subst j
          exact fieldTypes i

/-- Theorem 24. Every step preserves typing in a location environment that
agrees with the old environment at every old location. An empty variable
environment is retained for both the expression and the stored values. -/
theorem preservation {Θ : LocTypes} {before after : Config} {T : Ty}
    (step : Step before after) (typed : HasType Θ .empty before.expr T)
    (store : StoreTyped Θ before.store) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty after.expr T ∧ StoreTyped Θ' after.store := by
  induction step generalizing Θ T with
  | add =>
      cases typed
      exact ⟨Θ, LocTypes.Extends.refl Θ, .int _, store⟩
  | ge =>
      cases typed
      exact ⟨Θ, LocTypes.Extends.refl Θ, .bool _, store⟩
  | binaryLeft _ ih =>
      cases typed with
      | add hl hr =>
          obtain ⟨Θ', extension, hl', store'⟩ := ih hl store
          exact ⟨Θ', extension, .add hl' (hr.weakenLocs extension), store'⟩
      | ge hl hr =>
          obtain ⟨Θ', extension, hl', store'⟩ := ih hl store
          exact ⟨Θ', extension, .ge hl' (hr.weakenLocs extension), store'⟩
  | binaryRight _ _ ih =>
      cases typed with
      | add hl hr =>
          obtain ⟨Θ', extension, hr', store'⟩ := ih hr store
          exact ⟨Θ', extension, .add (hl.weakenLocs extension) hr', store'⟩
      | ge hl hr =>
          obtain ⟨Θ', extension, hr', store'⟩ := ih hr store
          exact ⟨Θ', extension, .ge (hl.weakenLocs extension) hr', store'⟩
  | seqSkip =>
      cases typed with
      | seq _ hr => exact ⟨Θ, LocTypes.Extends.refl Θ, hr, store⟩
  | seqStep _ ih =>
      cases typed with
      | seq hl hr =>
          obtain ⟨Θ', extension, hl', store'⟩ := ih hl store
          exact ⟨Θ', extension, .seq hl' (hr.weakenLocs extension), store'⟩
  | ifTrue =>
      cases typed with
      | cond _ hy _ => exact ⟨Θ, LocTypes.Extends.refl Θ, hy, store⟩
  | ifFalse =>
      cases typed with
      | cond _ _ hn => exact ⟨Θ, LocTypes.Extends.refl Θ, hn, store⟩
  | ifStep _ ih =>
      cases typed with
      | cond hc hy hn =>
          obtain ⟨Θ', extension, hc', store'⟩ := ih hc store
          exact ⟨Θ', extension, .cond hc' (hy.weakenLocs extension) (hn.weakenLocs extension), store'⟩
  | «while» =>
      cases typed with
      | loop ht hb => exact ⟨Θ, LocTypes.Extends.refl Θ, .cond ht (.seq hb (.loop ht hb)) .skip, store⟩
  | appLeft _ ih =>
      cases typed with
      | app hf ha =>
          obtain ⟨Θ', extension, hf', store'⟩ := ih hf store
          exact ⟨Θ', extension, .app hf' (ha.weakenLocs extension), store'⟩
  | appRight _ _ ih =>
      cases typed with
      | app hf ha =>
          obtain ⟨Θ', extension, ha', store'⟩ := ih ha store
          exact ⟨Θ', extension, .app (hf.weakenLocs extension) ha', store'⟩
  | appFun =>
      cases typed with
      | app hf ha =>
          cases hf with
          | lam hb => exact ⟨Θ, LocTypes.Extends.refl Θ, hb.beta ha, store⟩
  | letStep _ ih =>
      cases typed with
      | letE hv hb =>
          obtain ⟨Θ', extension, hv', store'⟩ := ih hv store
          exact ⟨Θ', extension, .letE hv' (hb.weakenLocs extension), store'⟩
  | letValue =>
      cases typed with
      | letE hv hb => exact ⟨Θ, LocTypes.Extends.refl Θ, hb.beta hv, store⟩
  | letRecFun =>
      cases typed with
      | letRecFun hf hb => exact ⟨Θ, LocTypes.Extends.refl Θ, hb.beta hf.recClosure, store⟩
  | pairLeft _ ih =>
      cases typed with
      | pair hl hr =>
          obtain ⟨Θ', extension, hl', store'⟩ := ih hl store
          exact ⟨Θ', extension, .pair hl' (hr.weakenLocs extension), store'⟩
  | pairRight _ _ ih =>
      cases typed with
      | pair hl hr =>
          obtain ⟨Θ', extension, hr', store'⟩ := ih hr store
          exact ⟨Θ', extension, .pair (hl.weakenLocs extension) hr', store'⟩
  | fstValue =>
      cases typed with
      | fst hp =>
          cases hp with
          | pair hl _ => exact ⟨Θ, LocTypes.Extends.refl Θ, hl, store⟩
  | sndValue =>
      cases typed with
      | snd hp =>
          cases hp with
          | pair _ hr => exact ⟨Θ, LocTypes.Extends.refl Θ, hr, store⟩
  | fstStep _ ih =>
      cases typed with
      | fst hp =>
          obtain ⟨Θ', extension, hp', store'⟩ := ih hp store
          exact ⟨Θ', extension, .fst hp', store'⟩
  | sndStep _ ih =>
      cases typed with
      | snd hp =>
          obtain ⟨Θ', extension, hp', store'⟩ := ih hp store
          exact ⟨Θ', extension, .snd hp', store'⟩
  | inl _ ih =>
      cases typed with
      | inl he =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .inl he', store'⟩
  | inr _ ih =>
      cases typed with
      | inr he =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .inr he', store'⟩
  | matchStep _ ih =>
      cases typed with
      | matchSum he hl hr =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .matchSum he' (hl.weakenLocs extension) (hr.weakenLocs extension), store'⟩
  | matchLeft =>
      cases typed with
      | matchSum he hl _ =>
          cases he with
          | inl hv => exact ⟨Θ, LocTypes.Extends.refl Θ, hl.beta hv, store⟩
  | matchRight =>
      cases typed with
      | matchSum he _ hr =>
          cases he with
          | inr hv => exact ⟨Θ, LocTypes.Extends.refl Θ, hr.beta hv, store⟩
  | recordStep i _ _ ih =>
      cases typed with
      | record fields =>
          obtain ⟨Θ', extension, updated, store'⟩ := ih (fields i) store
          refine ⟨Θ', extension, .record (fun j => ?_), store'⟩
          by_cases same : j = i
          · subst j
            simpa only [Function.update_self] using updated
          · simpa only [Function.update_of_ne same] using (fields j).weakenLocs extension
  | projectValue i _ =>
      exact ⟨Θ, LocTypes.Extends.refl Θ, record_projection_type typed rfl, store⟩
  | projectStep _ ih =>
      cases typed with
      | project i he =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .project i he', store'⟩
  | @refValue _ value address fresh =>
      cases typed with
      | @ref _ _ contentsType hv =>
          have extension : Θ.Extends (Θ.insert address contentsType) :=
            LocTypes.extends_insert (fun present => fresh ((store.domain address).mp present))
          exact ⟨_, extension, .loc (Finmap.lookup_insert Θ), store.insert hv extension⟩
  | refStep _ ih =>
      cases typed with
      | ref he =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .ref he', store'⟩
  | derefValue present =>
      cases typed with
      | deref hl =>
          cases hl with
          | loc lookup => exact ⟨Θ, LocTypes.Extends.refl Θ, store.contents lookup present, store⟩
  | derefStep _ ih =>
      cases typed with
      | deref he =>
          obtain ⟨Θ', extension, he', store'⟩ := ih he store
          exact ⟨Θ', extension, .deref he', store'⟩
  | assignValue =>
      cases typed with
      | assign hl hv =>
          cases hl with
          | loc lookup => exact ⟨Θ, LocTypes.Extends.refl Θ, .skip, store.assign hv lookup⟩
  | assignRight _ ih =>
      cases typed with
      | assign hl hr =>
          obtain ⟨Θ', extension, hr', store'⟩ := ih hr store
          exact ⟨Θ', extension, .assign (hl.weakenLocs extension) hr', store'⟩
  | assignLeft _ ih =>
      cases typed with
      | assign hl hr =>
          obtain ⟨Θ', extension, hl', store'⟩ := ih hl store
          exact ⟨Θ', extension, .assign hl' (hr.weakenLocs extension), store'⟩

theorem preservation_steps {Θ : LocTypes} {before after : Config} {T : Ty}
    (steps : Steps before after) (typed : HasType Θ .empty before.expr T)
    (store : StoreTyped Θ before.store) :
    ∃ Θ', Θ.Extends Θ' ∧ HasType Θ' .empty after.expr T ∧ StoreTyped Θ' after.store := by
  induction steps with
  | refl => exact ⟨Θ, LocTypes.Extends.refl Θ, typed, store⟩
  | tail _ step ih =>
      obtain ⟨Θ', extension, typed', store'⟩ := ih
      obtain ⟨Θ'', extension', typed'', store''⟩ := preservation step typed' store'
      exact ⟨Θ'', extension.trans extension', typed'', store''⟩

/-- Theorem 25. Well-typed configurations cannot reach a stuck state in any
finite execution, including every allowed choice of fresh location. -/
theorem safety {Θ : LocTypes} {before after : Config} {T : Ty}
    (steps : Steps before after) (typed : HasType Θ .empty before.expr T)
    (store : StoreTyped Θ before.store) : ¬ Stuck after := by
  obtain ⟨_, _, typed', store'⟩ := preservation_steps steps typed store
  intro ⟨notValue, noStep⟩
  rcases progress typed' store' with value | ⟨next, step⟩
  · exact notValue value
  · exact noStep next step

end Silmaril.Courses.Cambridge.L3
