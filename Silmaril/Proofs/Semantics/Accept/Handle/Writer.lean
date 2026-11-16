module

public import Silmaril.Semantics.Accept.Handle.Defs
public import Silmaril.Semantics.Accept.Host.Thms
public import Mathlib.Data.Fintype.Card

/-! # Proofs: writer policies, fixed environments, persistence and capacity -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H]
variable {W : Writer Op X}

/-! ## Store extension -/

omit [DecidableEq H] in
theorem extends_refl (σ : Env H X) : σ.Extends σ := fun _ _ h => h

omit [DecidableEq H] in
theorem extends_trans {σ σ' σ'' : Env H X} (h₁ : σ.Extends σ') (h₂ : σ'.Extends σ'') :
    σ.Extends σ'' := fun _ _ h => h₂ (h₁ h)

theorem extends_update_of_fresh {pol : Policy H} {σ : Env H X} {r : H} {t : X}
    (hf : Fresh pol σ r t) : σ.Extends (Function.update σ r (some t)) := by
  intro h x hx
  by_cases hh : h = r
  · subst hh
    rcases hf.2 with hn | ⟨_, hs⟩
    · simp [hn] at hx
    · rw [hs] at hx; simpa using hx
  · simpa [Function.update_of_ne hh] using hx

theorem wstep_extends {pol : Policy H} {fix : Option (Env H X)} {s s' : WState H X}
    {e : WEv Op H} {A : Set X} (hs : WStep W pol fix s e s' A) : s.store.Extends s'.store := by
  cases hs with
  | writeOk _ hf _ => exact extends_update_of_fresh hf
  | writeFixed _ _ _ _ hf _ => exact extends_update_of_fresh hf
  | _ => exact extends_refl _

theorem run_extends {pol : Policy H} {fix : Option (Env H X)} {s s' : WState H X}
    {t : List (WEv Op H)} {A : Set X} (hr : (writer W pol fix).Run s t s' A) :
    s.store.Extends s'.store := by
  induction hr with
  | nil => exact extends_refl _
  | cons hs _ ih => exact extends_trans (wstep_extends hs) ih

/-! ## Policy order -/

omit [DecidableEq H] in
theorem fresh_mono {pol pol' : Policy H} (hle : pol.Le pol') {σ : Env H X} {r : H} {t : X}
    (hf : Fresh pol σ r t) : Fresh pol' σ r t := by
  obtain ⟨hs, hi, -, -⟩ := hle
  refine ⟨hs ▸ hf.1, ?_⟩
  rcases hf.2 with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨hi h1, h2⟩

omit [DecidableEq H] in
theorem agrees_none {r : H} {t : X} : Agrees (none : Option (Env H X)) r t := by
  intro ρ h; cases h

/-- The simulation relation of the policy order. -/
def LeRel (s₁ s₂ : WState H X) : Prop := s₁ = s₂ ∨ s₁.phase = .dead ∨ s₂.phase = .chaos

theorem sim_le {pol pol' : Policy H} (hle : pol.Le pol') :
    Sim (writer W pol) (writer W pol') id (LeRel (H := H) (X := X)) := by
  refine ⟨.inl rfl, ?_⟩
  rintro s₁ s₂ e s₁' A hR hs
  rcases hR with rfl | hd | hc
  · obtain ⟨hsen, -, hacc, hwr⟩ := id hle
    cases hs with
    | writeOk hb hf _ => exact ⟨_, _, .writeOk hb (fresh_mono hle hf) agrees_none, .inl rfl, le_rfl⟩
    | writeFail hsn hc =>
        rcases hc with hc | hc
        · exact ⟨_, _, .writeFail (hsen ▸ hsn) (.inl hc), .inl rfl, le_rfl⟩
        · rcases hw : pol'.onWrite with _ | _ | _
          · simp [OnBadWrite.rank, hc, hw] at hwr
          · exact ⟨_, _, .writeFail (hsen ▸ hsn) (.inr hw), .inl rfl, le_rfl⟩
          · rcases hb : W.built _ _ _ with _ | t
            · exact ⟨_, _, .writeChaos hb hw rfl, .inr (.inr rfl), Set.subset_univ _⟩
            · exact ⟨_, _, .writeFail (hsen ▸ hsn) (.inl (by simp [hb])), .inl rfl, le_rfl⟩
    | writeChaos hb hu _ =>
        have hw : pol'.onWrite = .ub := by
          rcases hw : pol'.onWrite with _ | _ | _ <;> simp [OnBadWrite.rank, hu, hw] at hwr ⊢
        exact ⟨_, _, .writeChaos hb hw rfl, .inr (.inr rfl), le_rfl⟩
    | writeFixed _ _ hfix => cases hfix
    | acceptOk h => exact ⟨_, _, .acceptOk h, .inl rfl, le_rfl⟩
    | acceptTrap h hp =>
        rcases ha : pol'.onAccept with _ | _ | _
        · exact ⟨_, _, .acceptTrap h ha, .inl rfl, le_rfl⟩
        · exact ⟨_, _, .acceptIgnore h ha, .inr (.inl rfl), le_rfl⟩
        · exact ⟨_, _, .acceptChaos h ha rfl, .inr (.inr rfl), Set.empty_subset _⟩
    | acceptIgnore h hp =>
        rcases ha : pol'.onAccept with _ | _ | _
        · simp [OnInvalid.rank, hp, ha] at hacc
        · exact ⟨_, _, .acceptIgnore h ha, .inl rfl, le_rfl⟩
        · exact ⟨_, _, .acceptChaos h ha rfl, .inr (.inr rfl), Set.empty_subset _⟩
    | acceptChaos h hp _ =>
        have ha : pol'.onAccept = .ub := by
          rcases ha : pol'.onAccept with _ | _ | _ <;> simp [OnInvalid.rank, hp, ha] at hacc ⊢
        exact ⟨_, _, .acceptChaos h ha rfl, .inr (.inr rfl), le_rfl⟩
    | acceptFixed _ _ hfix => cases hfix
    | acceptErrOk h => exact ⟨_, _, .acceptErrOk h, .inl rfl, le_rfl⟩
    | acceptErrBad h => exact ⟨_, _, .acceptErrBad h, .inl rfl, le_rfl⟩
    | acceptAll => exact ⟨_, _, .acceptAll, .inl rfl, le_rfl⟩
    | acceptBatch k => exact ⟨_, _, .acceptBatch k, .inl rfl, le_rfl⟩
    | chaos e => exact ⟨_, _, .chaos e, .inl rfl, le_rfl⟩
  · cases hs <;> simp at hd
  · obtain ⟨σ, B, p⟩ := s₂
    simp only at hc
    subst hc
    exact ⟨_, _, .chaos e, .inr (.inr rfl), Set.subset_univ _⟩

theorem writerLang_mono {pol pol' : Policy H} (hle : pol.Le pol') (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ writerLang W pol' T :=
  lang_subset_of_sim_id (sim_le hle) T

/-! ## Fixed environments -/

/-- A fixed environment is a restriction of the store semantics with `ub` as top. -/
theorem sim_fixed (pol : Policy H) (ρ : Env H X) :
    Sim (writer W pol (some ρ)) (writer W pol) id (fun s₁ s₂ => s₁ = s₂ ∨ s₂.phase = .chaos) := by
  refine ⟨.inl rfl, ?_⟩
  rintro s₁ s₂ e s₁' A hR hs
  rcases hR with rfl | hc
  · cases hs with
    | writeOk hb hf _ => exact ⟨_, _, .writeOk hb hf agrees_none, .inl rfl, le_rfl⟩
    | writeFail hsn hc => exact ⟨_, _, .writeFail hsn hc, .inl rfl, le_rfl⟩
    | writeChaos _ _ hfix => cases hfix
    | writeFixed hb hu _ _ _ _ => exact ⟨_, _, .writeChaos hb hu rfl, .inr rfl, Set.subset_univ _⟩
    | acceptOk h => exact ⟨_, _, .acceptOk h, .inl rfl, le_rfl⟩
    | acceptTrap h hp => exact ⟨_, _, .acceptTrap h hp, .inl rfl, le_rfl⟩
    | acceptIgnore h hp => exact ⟨_, _, .acceptIgnore h hp, .inl rfl, le_rfl⟩
    | acceptChaos _ _ hfix => cases hfix
    | acceptFixed h hp _ => exact ⟨_, _, .acceptChaos h hp rfl, .inr rfl, Set.subset_univ _⟩
    | acceptErrOk h => exact ⟨_, _, .acceptErrOk h, .inl rfl, le_rfl⟩
    | acceptErrBad h => exact ⟨_, _, .acceptErrBad h, .inl rfl, le_rfl⟩
    | acceptAll => exact ⟨_, _, .acceptAll, .inl rfl, le_rfl⟩
    | acceptBatch k => exact ⟨_, _, .acceptBatch k, .inl rfl, le_rfl⟩
    | chaos e => exact ⟨_, _, .chaos e, .inl rfl, le_rfl⟩
  · obtain ⟨σ, B, p⟩ := s₂
    simp only at hc
    subst hc
    exact ⟨_, _, .chaos e, .inr rfl, Set.subset_univ _⟩

theorem fixedLang_subset (pol : Policy H) (Envs : Set (Env H X)) (T : Set (List (WEv Op H))) :
    fixedLang W pol Envs T ⊆ writerLang W pol T := by
  intro x hx
  simp only [fixedLang, langOver, Set.mem_iUnion] at hx
  obtain ⟨ρ, hx⟩ := hx
  exact lang_subset_of_sim_id (sim_fixed pol ρ.1) T hx

/-- The store run of a policy without write UB is a fixed-environment run (with UB accepts
resolved through `ρ`) for every `ρ` extending its final store. -/
theorem run_fixed {pol : Policy H} (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (ρ : Env H X) :
    ∀ {s s' : WState H X} {t : List (WEv Op H)} {A : Set X},
      (writer W pol).Run s t s' A → s'.store.Extends ρ →
      ∃ s₂ B, (writer W {pol with onAccept := .ub} (some ρ)).Run s t s₂ B ∧ A ⊆ B := by
  intro s s' t A hr hρ
  induction hr with
  | nil s => exact ⟨s, ∅, .nil s, le_rfl⟩
  | @cons s s₁ s₂ e es A' B' hs hrest ih =>
      have hρ₁ : s₁.store.Extends ρ := extends_trans (run_extends hrest) hρ
      obtain ⟨s₃, B₃, hr₃, hAB⟩ := ih hρ
      -- the step itself
      have step : ∃ s₁' C, WStep W {pol with onAccept := .ub} (some ρ) s e s₁' C ∧ A' ⊆ C ∧
          (s₁' = s₁ ∨ (s₁.phase = .dead ∧ es = [] )) := by
        cases hs with
        | writeOk hb hf _ =>
            refine ⟨_, _, .writeOk hb hf ?_, le_rfl, .inl rfl⟩
            intro ρ' h; cases h
            exact hρ₁ (by simp)
        | writeFail hsn hc => exact ⟨_, _, .writeFail hsn hc, le_rfl, .inl rfl⟩
        | writeChaos _ hu _ => exact absurd hu hw
        | writeFixed _ _ hfix => cases hfix
        | acceptOk h => exact ⟨_, _, .acceptOk h, le_rfl, .inl rfl⟩
        | acceptTrap h _ =>
            refine ⟨_, _, .acceptFixed h rfl rfl, Set.empty_subset _, .inr ⟨rfl, ?_⟩⟩
            cases hrest with
            | nil => rfl
            | cons hs' _ => cases hs'
        | acceptIgnore h _ => exact ⟨_, _, .acceptFixed h rfl rfl, Set.empty_subset _, .inl rfl⟩
        | acceptChaos _ hu _ => exact absurd hu ha
        | acceptFixed _ _ hfix => cases hfix
        | acceptErrOk h => exact ⟨_, _, .acceptErrOk h, le_rfl, .inl rfl⟩
        | acceptErrBad h => exact ⟨_, _, .acceptErrBad h, le_rfl, .inl rfl⟩
        | acceptAll => exact ⟨_, _, .acceptAll, le_rfl, .inl rfl⟩
        | acceptBatch k => exact ⟨_, _, .acceptBatch k, le_rfl, .inl rfl⟩
        | chaos e => exact ⟨_, _, .chaos e, le_rfl, .inl rfl⟩
      obtain ⟨s₁', C, hC, hAC, h₁⟩ := step
      rcases h₁ with rfl | ⟨-, rfl⟩
      · exact ⟨s₃, C ∪ B₃, .cons hC hr₃, Set.union_subset_union hAC hAB⟩
      · cases hrest
        exact ⟨s₁', C ∪ ∅, .cons hC (.nil _), Set.union_subset_union hAC le_rfl⟩

end Silmaril.Proofs.Semantics.Accept.Handle

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H]
variable {W : Writer Op X}

theorem writerLang_subset_fixedLang {pol : Policy H} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ fixedLang W {pol with onAccept := .ub} Set.univ T := by
  intro x hx
  simp only [writerLang, mem_lang] at hx
  obtain ⟨t, ht, s, A, hr, hxA⟩ := hx
  obtain ⟨s₂, B, hr₂, hAB⟩ := run_fixed hw ha s.store hr (extends_refl _)
  simp only [fixedLang, langOver, Set.mem_iUnion]
  exact ⟨⟨s.store, Set.mem_univ _⟩, mem_lang.2 ⟨t, ht, s₂, B, hr₂, hAB hxA⟩⟩

/-! ## Capacity -/

theorem mem_successes {pol : Policy H} {h : H} :
    ∀ {t : List (WEv Op H)}, h ∈ successes pol t → pol.sentinel ≠ some h
  | [], hm => by simp [successes] at hm
  | .write _ _ r :: es, hm => by
      simp only [successes] at hm
      split at hm
      · exact mem_successes hm
      · rcases List.mem_cons.1 hm with rfl | hm
        · assumption
        · exact mem_successes hm
  | .accept _ :: es, hm => mem_successes (t := es) hm
  | .acceptErr _ _ :: es, hm => mem_successes (t := es) hm
  | .acceptAll :: es, hm => mem_successes (t := es) hm
  | .acceptBatch _ :: es, hm => mem_successes (t := es) hm

theorem successes_fresh {pol : Policy H} (hi : pol.intern = false) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    ∀ {s s' : WState H X} {t : List (WEv Op H)} {A : Set X}, (writer W pol).Run s t s' A →
      s.phase ≠ .chaos → (successes pol t).Nodup ∧ ∀ h ∈ successes pol t, s.store h = none := by
  intro s s' t A hr hc
  induction hr with
  | nil => simp [successes]
  | cons hs hrest ih =>
      cases hs with
      | @writeOk σ B op args r t hb hf _ =>
          obtain ⟨hnd, hall⟩ := ih (by simp)
          have hr0 : σ r = none := by
            rcases hf.2 with h | ⟨h, _⟩
            · exact h
            · simp [hi] at h
          simp only [successes, hf.1, ite_false]
          refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
          · have := hall r hm; simp at this
          · intro h hm
            rcases List.mem_cons.1 hm with rfl | hm
            · exact hr0
            · have := hall h hm
              by_cases hh : h = r
              · subst hh; simp at this
              · simpa [Function.update_of_ne hh] using this
      | writeFail hsn _ =>
          simp only [successes, hsn, ite_true]; exact ih (by simp)
      | writeChaos _ hu _ => exact absurd hu hw
      | writeFixed _ _ hfix => cases hfix
      | acceptOk _ => exact ih (by simp)
      | acceptTrap _ _ => exact ih (by simp)
      | acceptIgnore _ _ => exact ih (by simp)
      | acceptChaos _ hu _ => exact absurd hu ha
      | acceptFixed _ _ hfix => cases hfix
      | acceptErrOk _ => exact ih (by simp)
      | acceptErrBad _ => exact ih (by simp)
      | acceptAll => exact ih (by simp)
      | acceptBatch _ => exact ih (by simp)
      | chaos _ => exact absurd rfl hc

theorem successes_length_le [Fintype H] {pol : Policy H} (hi : pol.intern = false)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s' : WState H X}
    {t : List (WEv Op H)} {A : Set X} (hr : (writer W pol).Run WState.init t s' A) :
    (successes pol t).length ≤ (Finset.univ.filter fun h => pol.sentinel ≠ some h).card := by
  have hnd := (successes_fresh hi hw ha hr (by simp [WState.init])).1
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro h hh
  simp only [List.mem_toFinset] at hh
  simpa using mem_successes hh

/-! ## The constructed set -/

omit [DecidableEq H] in
theorem lookupAll_mem {σ : Env H X} :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → ∀ c ∈ ts, c ∈ σ.range
  | [], ts, h => by simp [Env.lookupAll] at h; subst h; simp
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact ⟨h₀, hx⟩
      · exact lookupAll_mem (hs := hs) hxs c hc

theorem range_downClosed_update {Sub : X → X → Prop} (hW : W.ChildRel Sub) {pol : Policy H}
    {σ : Env H X} {op : Op} {args : List H} {r : H} {t : X} (hb : W.built σ op args = some t)
    (hf : Fresh pol σ r t) (hd : DownClosed Sub σ.range) :
    DownClosed Sub (Env.range (Function.update σ r (some t))) := by
  have hext := extends_update_of_fresh hf
  rintro x ⟨h, hx⟩ c hc
  by_cases hh : h = r
  · subst hh
    simp only [Function.update_self, Option.some.injEq] at hx
    subst hx
    simp only [Writer.built, Option.bind_eq_some_iff] at hb
    obtain ⟨ts, hts, hbt⟩ := hb
    obtain ⟨h', h'c⟩ := lookupAll_mem hts c (hW hbt c hc)
    exact ⟨h', hext h'c⟩
  · rw [Function.update_of_ne hh] at hx
    obtain ⟨h', h'c⟩ := hd ⟨h, hx⟩ hc
    exact ⟨h', hext h'c⟩

theorem downClosed_union {Sub : X → X → Prop} {A B : Set X} (hA : DownClosed Sub A)
    (hB : DownClosed Sub B) : DownClosed Sub (A ∪ B) := by
  rintro t (ht | ht) c hc
  · exact .inl (hA ht hc)
  · exact .inr (hB ht hc)

theorem run_downClosed {Sub : X → X → Prop} (hW : W.ChildRel Sub) {pol : Policy H}
    (hw : pol.onWrite ≠ .ub) :
    ∀ {s s' : WState H X} {t : List (WEv Op H)} {A : Set X}, (writer W pol).Run s t s' A →
      s.phase ≠ .chaos → (∀ e ∈ t, AllOnly e) → DownClosed Sub s.store.range →
      DownClosed Sub A := by
  intro s s' t A hr hc hall hd
  induction hr with
  | nil => intro _ h; simp at h
  | cons hs hrest ih =>
      have hrest' : ∀ e ∈ _, AllOnly e := fun e he => hall e (List.mem_cons_of_mem _ he)
      have hhead := hall _ List.mem_cons_self
      cases hs with
      | writeOk hb hf _ =>
          exact downClosed_union (fun _ h => by simp at h)
            (ih (by simp) hrest' (range_downClosed_update hW hb hf hd))
      | writeFail _ _ =>
          exact downClosed_union (fun _ h => by simp at h) (ih (by simp) hrest' hd)
      | writeChaos _ hu _ => exact absurd hu hw
      | writeFixed _ _ hfix => cases hfix
      | acceptAll => exact downClosed_union hd (ih (by simp) hrest' hd)
      | chaos _ => exact absurd rfl hc
      | _ => simp [AllOnly] at hhead

theorem writerLang_downClosed {Sub : X → X → Prop} (hW : W.ChildRel Sub) {pol : Policy H}
    (hw : pol.onWrite ≠ .ub) {T : Set (List (WEv Op H))} (hT : ∀ t ∈ T, ∀ e ∈ t, AllOnly e) :
    DownClosed Sub (writerLang W pol T) := by
  intro x hx c hc
  simp only [writerLang, mem_lang] at hx ⊢
  obtain ⟨t, ht, s, A, hr, hxA⟩ := hx
  refine ⟨t, ht, s, A, hr, run_downClosed hW hw hr (by simp [writer, WState.init]) (hT t ht)
    ?_ hxA hc⟩
  rintro y ⟨h, hy⟩; simp [writer, WState.init, Env.empty] at hy

/-! ## Error-return accept -/

theorem sim_eraseErr {pol : Policy H} (ha : pol.onAccept ≠ .ub) :
    Sim (writer W pol) (writer W {pol with onAccept := .ignore}) WEv.eraseErr
      (LeRel (H := H) (X := X)) := by
  refine ⟨.inl rfl, ?_⟩
  rintro s₁ s₂ e s₁' A hR hs
  rcases hR with rfl | hd | hc
  · cases hs with
    | writeOk hb hf _ => exact ⟨_, _, .writeOk hb hf agrees_none, .inl rfl, le_rfl⟩
    | writeFail hsn hc => exact ⟨_, _, .writeFail hsn hc, .inl rfl, le_rfl⟩
    | writeChaos hb hu _ => exact ⟨_, _, .writeChaos hb hu rfl, .inl rfl, le_rfl⟩
    | writeFixed _ _ hfix => cases hfix
    | acceptOk h => exact ⟨_, _, .acceptOk h, .inl rfl, le_rfl⟩
    | acceptTrap h _ => exact ⟨_, _, .acceptIgnore h rfl, .inr (.inl rfl), le_rfl⟩
    | acceptIgnore h _ => exact ⟨_, _, .acceptIgnore h rfl, .inl rfl, le_rfl⟩
    | acceptChaos _ hu _ => exact absurd hu ha
    | acceptFixed _ _ hfix => cases hfix
    | acceptErrOk h => exact ⟨_, _, .acceptOk h, .inl rfl, le_rfl⟩
    | acceptErrBad h => exact ⟨_, _, .acceptIgnore h rfl, .inl rfl, le_rfl⟩
    | acceptAll => exact ⟨_, _, .acceptAll, .inl rfl, le_rfl⟩
    | acceptBatch k => exact ⟨_, _, .acceptBatch k, .inl rfl, le_rfl⟩
    | chaos e => exact ⟨_, _, .chaos _, .inl rfl, le_rfl⟩
  · cases hs <;> simp at hd
  · obtain ⟨σ, B, p⟩ := s₂
    simp only at hc
    subst hc
    exact ⟨_, _, .chaos _, .inr (.inr rfl), Set.subset_univ _⟩

theorem writerLang_subset_eraseErr {pol : Policy H} (ha : pol.onAccept ≠ .ub)
    (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ writerLang W {pol with onAccept := .ignore} (List.map WEv.eraseErr '' T) :=
  lang_subset_of_sim (sim_eraseErr ha) T

theorem run_unerase {pol : Policy H} (ha : pol.onAccept = .ignore) :
    ∀ {t : List (WEv Op H)} {s s' : WState H X} {A : Set X},
      (writer W pol).Run s (t.map WEv.eraseErr) s' A →
      ∃ t', t'.map WEv.eraseErr = t.map WEv.eraseErr ∧ (writer W pol).Run s t' s' A
  | [], s, s', A, hr => ⟨[], rfl, by simpa using hr⟩
  | e :: es, s, s', A, hr => by
      cases hr with
      | cons hs hrest =>
          obtain ⟨t', ht', hr'⟩ := run_unerase ha hrest
          cases e with
          | acceptErr h b =>
              cases hs with
              | acceptOk hh =>
                  exact ⟨.acceptErr h true :: t', by simp [WEv.eraseErr, ht'], .cons (.acceptErrOk hh) hr'⟩
              | acceptIgnore hh _ =>
                  exact ⟨.acceptErr h false :: t', by simp [WEv.eraseErr, ht'], .cons (.acceptErrBad hh) hr'⟩
              | acceptTrap _ hp => rw [ha] at hp; cases hp
              | acceptChaos _ hp _ => rw [ha] at hp; cases hp
              | acceptFixed _ _ hfix => cases hfix
              | chaos _ => exact ⟨.acceptErr h b :: t', by simp [WEv.eraseErr, ht'], .cons (.chaos _) hr'⟩
          | write op args r => exact ⟨_ :: t', by simp [WEv.eraseErr, ht'], .cons hs hr'⟩
          | accept h => exact ⟨_ :: t', by simp [WEv.eraseErr, ht'], .cons hs hr'⟩
          | acceptAll => exact ⟨_ :: t', by simp [WEv.eraseErr, ht'], .cons hs hr'⟩
          | acceptBatch k => exact ⟨_ :: t', by simp [WEv.eraseErr, ht'], .cons hs hr'⟩

theorem writerLang_eraseErr_eq {pol : Policy H} (ha : pol.onAccept = .ignore)
    {T : Set (List (WEv Op H))} (hT : ResultOblivious T) :
    writerLang W pol (List.map WEv.eraseErr '' T) = writerLang W pol T := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [writerLang, mem_lang] at hx ⊢
    obtain ⟨_, ⟨t, ht, rfl⟩, s, A, hr, hxA⟩ := hx
    obtain ⟨t', ht', hr'⟩ := run_unerase ha hr
    exact ⟨t', hT t ht t' ht', s, A, hr', hxA⟩
  · have hpol : ({pol with onAccept := .ignore} : Policy H) = pol := by
      cases pol; simp_all
    have := writerLang_subset_eraseErr (W := W) (pol := pol) (by simp [ha]) T
    rwa [hpol] at this

end Silmaril.Proofs.Semantics.Accept.Handle

namespace Silmaril.Proofs.Semantics.Accept.Handle

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Host

universe u v w

variable {Op : Type u} {H : Type v} {X : Type w} [DecidableEq H]
variable {W : Writer Op X}

/-! ## Sentinels -/

omit [DecidableEq H] in
theorem fresh_sentinel_iff {pol : Policy H} {s : H} (hs : pol.sentinel = some s) {σ : Env H X}
    {r : H} {t : X} (hr : r ≠ s) : Fresh pol σ r t ↔ Fresh {pol with sentinel := none} σ r t := by
  simp only [Fresh, hs, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true, true_and]
  exact ⟨fun h => h.2, fun h => ⟨fun e => hr e.symm, h⟩⟩

/-- Away from writes returning the sentinel, a sentinel policy answers as the policy without
one. -/
theorem wstep_sentinel_iff {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    {fix : Option (Env H X)} {st st' : WState H X} {e : WEv Op H} {A : Set X}
    (he : ∀ op args, e ≠ .write op args s) :
    WStep W pol fix st e st' A ↔ WStep W {pol with sentinel := none} fix st e st' A := by
  constructor
  · intro h
    cases h with
    | @writeOk σ B op args r t hb hf ha =>
        have hr : r ≠ s := fun e => he op args (by rw [e])
        exact .writeOk hb ((fresh_sentinel_iff hs hr).1 hf) ha
    | @writeFail σ B op args r hsn _ =>
        rw [hs] at hsn; cases hsn; exact absurd rfl (he op args)
    | writeChaos hb hu hf => exact .writeChaos hb hu hf
    | @writeFixed σ B op args r t ρ hb hu hfix hb' hf hρ =>
        have hr : r ≠ s := fun e => he op args (by rw [e])
        exact .writeFixed hb hu hfix hb' ((fresh_sentinel_iff hs hr).1 hf) hρ
    | acceptOk h => exact .acceptOk h
    | acceptTrap h hp => exact .acceptTrap h hp
    | acceptIgnore h hp => exact .acceptIgnore h hp
    | acceptChaos h hp hf => exact .acceptChaos h hp hf
    | acceptFixed h hp hf => exact .acceptFixed h hp hf
    | acceptErrOk h => exact .acceptErrOk h
    | acceptErrBad h => exact .acceptErrBad h
    | acceptAll => exact .acceptAll
    | acceptBatch k => exact .acceptBatch k
    | chaos e => exact .chaos e
  · intro h
    cases h with
    | @writeOk σ B op args r t hb hf ha =>
        have hr : r ≠ s := fun e => he op args (by rw [e])
        exact .writeOk hb ((fresh_sentinel_iff hs hr).2 hf) ha
    | writeFail hsn _ => cases hsn
    | writeChaos hb hu hf => exact .writeChaos hb hu hf
    | @writeFixed σ B op args r t ρ hb hu hfix hb' hf hρ =>
        have hr : r ≠ s := fun e => he op args (by rw [e])
        exact .writeFixed hb hu hfix hb' ((fresh_sentinel_iff hs hr).2 hf) hρ
    | acceptOk h => exact .acceptOk h
    | acceptTrap h hp => exact .acceptTrap h hp
    | acceptIgnore h hp => exact .acceptIgnore h hp
    | acceptChaos h hp hf => exact .acceptChaos h hp hf
    | acceptFixed h hp hf => exact .acceptFixed h hp hf
    | acceptErrOk h => exact .acceptErrOk h
    | acceptErrBad h => exact .acceptErrBad h
    | acceptAll => exact .acceptAll
    | acceptBatch k => exact .acceptBatch k
    | chaos e => exact .chaos e

theorem writerLang_noRet {pol : Policy H} {s : H} (hs : pol.sentinel = some s)
    {T : Set (List (WEv Op H))} (hT : ∀ t ∈ T, NoRet s t) :
    writerLang W pol T = writerLang W {pol with sentinel := none} T :=
  Host.lang_congr (h := writer W pol) (h₂ := writer W {pol with sentinel := none})
    (fun e => ∀ op args, e ≠ .write op args s)
    (fun _ _ _ _ he => wstep_sentinel_iff hs he) rfl
    (fun t ht _ he op args h => hT t ht op args (h ▸ he))

/-! ## Renaming handles -/


omit [DecidableEq H] in
theorem lookupAll_rename (π : H ≃ H) (σ : Env H X) :
    ∀ args : List H, Env.lookupAll (σ ∘ π.symm) (args.map π) = σ.lookupAll args
  | [] => rfl
  | a :: args => by
      simp only [Env.lookupAll, List.map_cons, List.mapM_cons, Function.comp_apply,
        Equiv.symm_apply_apply] at *
      rw [show List.mapM (σ ∘ π.symm) (args.map π) = List.mapM σ args from
        lookupAll_rename π σ args]

omit [DecidableEq H] in
theorem built_rename (π : H ≃ H) (σ : Env H X) (op : Op) (args : List H) :
    W.built (σ ∘ π.symm) op (args.map π) = W.built σ op args := by
  simp [Writer.built, lookupAll_rename]

omit [DecidableEq H] in
theorem fresh_rename (π : H ≃ H) {pol : Policy H} {σ : Env H X} {r : H} {t : X} :
    Fresh (Policy.rename π pol) (σ ∘ π.symm) (π r) t ↔ Fresh pol σ r t := by
  simp only [Fresh, Policy.rename, Function.comp_apply, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => h1 (by rw [e]; rfl), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun e => h1 ?_, h2⟩
    rcases hs : pol.sentinel with _ | s
    · rw [hs] at e; cases e
    · rw [hs] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [π.injective e]

theorem update_rename (π : H ≃ H) (σ : Env H X) (r : H) (t : X) :
    Function.update (σ ∘ π.symm) (π r) (some t) = Function.update σ r (some t) ∘ π.symm := by
  funext h
  by_cases hh : h = π r
  · subst hh; simp
  · have : π.symm h ≠ r := fun e => hh (by rw [← e]; simp)
    simp [Function.update_of_ne hh, Function.update_of_ne this]

omit [DecidableEq H] in
theorem range_rename (π : H ≃ H) (σ : Env H X) : Env.range (σ ∘ π.symm) = σ.range := by
  ext x
  constructor
  · rintro ⟨h, hh⟩; exact ⟨_, hh⟩
  · rintro ⟨h, hh⟩; exact ⟨π h, by simpa using hh⟩

/-- The renaming relation on states. -/
def RenRel (π : H ≃ H) (s₁ s₂ : WState H X) : Prop :=
  s₂ = ⟨s₁.store ∘ π.symm, s₁.batch, s₁.phase⟩

theorem sim_rename (π : H ≃ H) (pol : Policy H) :
    Sim (writer W pol) (writer W (Policy.rename π pol)) (WEv.rename π) (RenRel (X := X) π) := by
  refine ⟨rfl, ?_⟩
  rintro s₁ s₂ e s₁' A hR hs
  subst hR
  cases hs with
  | @writeOk σ B op args r t hb hf _ =>
      refine ⟨_, _, .writeOk (by rw [built_rename]; exact hb) ((fresh_rename π).2 hf)
        agrees_none, ?_, le_rfl⟩
      simp [RenRel, update_rename]
  | @writeFail σ B op args r hsn hc =>
      refine ⟨_, _, .writeFail (by simp [Policy.rename, hsn]) ?_, rfl, le_rfl⟩
      simpa [built_rename, Policy.rename] using hc
  | writeChaos hb hu _ =>
      exact ⟨_, _, .writeChaos (by rw [built_rename]; exact hb) hu rfl, rfl, le_rfl⟩
  | writeFixed _ _ hfix => cases hfix
  | acceptOk h => exact ⟨_, _, .acceptOk (by simpa using h), rfl, le_rfl⟩
  | acceptTrap h hp => exact ⟨_, _, .acceptTrap (by simpa using h) hp, rfl, le_rfl⟩
  | acceptIgnore h hp => exact ⟨_, _, .acceptIgnore (by simpa using h) hp, rfl, le_rfl⟩
  | acceptChaos h hp _ => exact ⟨_, _, .acceptChaos (by simpa using h) hp rfl, rfl, le_rfl⟩
  | acceptFixed _ _ hfix => cases hfix
  | acceptErrOk h => exact ⟨_, _, .acceptErrOk (by simpa using h), rfl, le_rfl⟩
  | acceptErrBad h => exact ⟨_, _, .acceptErrBad (by simpa using h), rfl, le_rfl⟩
  | acceptAll => exact ⟨_, _, .acceptAll, rfl, by simp [range_rename]⟩
  | acceptBatch k => exact ⟨_, _, .acceptBatch k, rfl, le_rfl⟩
  | chaos e => exact ⟨_, _, .chaos _, rfl, le_rfl⟩

theorem writerLang_rename_subset (π : H ≃ H) (pol : Policy H) (T : Set (List (WEv Op H))) :
    writerLang W pol T ⊆ writerLang W (Policy.rename π pol) (List.map (WEv.rename π) '' T) :=
  lang_subset_of_sim (sim_rename π pol) T

omit [DecidableEq H] in
theorem rename_rename (π : H ≃ H) (e : WEv Op H) : WEv.rename π.symm (WEv.rename π e) = e := by
  cases e <;> simp [WEv.rename, List.map_map]

omit [DecidableEq H] in
theorem Policy.rename_symm (π : H ≃ H) (pol : Policy H) : Policy.rename π.symm (Policy.rename π pol) = pol := by
  cases pol with
  | mk s i a w => cases s <;> simp [Policy.rename]

theorem writerLang_rename (π : H ≃ H) (pol : Policy H) (T : Set (List (WEv Op H))) :
    writerLang W (Policy.rename π pol) (List.map (WEv.rename π) '' T) = writerLang W pol T := by
  apply Set.Subset.antisymm _ (writerLang_rename_subset π pol T)
  have h := writerLang_rename_subset (W := W) π.symm (Policy.rename π pol)
    (List.map (WEv.rename π) '' T)
  rw [Policy.rename_symm, Set.image_image] at h
  simpa [List.map_map, Function.comp_def, rename_rename] using h

end Silmaril.Proofs.Semantics.Accept.Handle
