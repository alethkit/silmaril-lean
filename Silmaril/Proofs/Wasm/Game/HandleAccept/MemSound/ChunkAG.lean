module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Exact.Defs
public import Silmaril.Semantics.Accept.Mixed.Thms
public import Silmaril.Semantics.Accept.Handle.Thms

/-!
# Proofs: assume/guarantee along the chunk buffer

`Silmaril.Accept.Mixed.mixedRel_subset_of_AG` constrains every return from every parsing state,
and its streaming variant (`mixedRel_subset_of_streamAG`) tracks the append buffer only: neither
can constrain `finish(n, h)` by the bytes it consumes. Here the guarantee is read **from the chunk
buffer along the trace**:

* `pstep_buf`: outside undefined behaviour a parsing step moves the chunk buffer by
  `Exact.chunkStep` (a `finish` overrun under `callTrap`/`ignore` leaves it, as `chunkStep` does);
* `mixedRel_subset_of_chunkAG` (store semantics, no undefined behaviour): if in every trace whose
  writes agree with `σ`, every return at `t = u ++ .p e :: v` from a parsing state whose buffer is
  `chunkFold [] (parseEvents u)` of a non-sentinel handle denoting `x` in `σ` relates
  `(w, x) ∈ R`, the relation is in `R`.

The run lemmas (no chaos, accepted pairs, writes agree with the final store) follow
`Silmaril.Proofs.Semantics.Accept.Mixed.Basic`, which the semantics topic does not export; they
are restated here for the store semantics.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ChunkAG

open Silmaril.Accept Silmaril.Accept.Handle Silmaril.Accept.Parse Silmaril.Accept.Mixed
  Silmaril.Wasm.Game.HandleAccept.MemSound.Exact

variable {Op V H X : Type}

/-! ## The chunk buffer -/

theorem returns_buf {ppol : PPolicy H} {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hr : Returns ppol s e w h s') : s'.buf = chunkStep s.buf e := by
  cases e with
  | parse v h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | done h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | finish n h' => obtain ⟨hn, -, -, rfl⟩ := hr; simp [chunkStep, hn]
  | append v => exact hr.elim
  | feed c => exact hr.elim
  | reset => exact hr.elim

theorem returns_phase {ppol : PPolicy H} {s s' : PState V} {e : PEv V H} {w : List V} {h : H}
    (hr : Returns ppol s e w h s') : s'.phase = s.phase := by
  cases e with
  | parse v h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | done h' => obtain ⟨-, -, rfl⟩ := hr; rfl
  | finish n h' => obtain ⟨-, -, -, rfl⟩ := hr; rfl
  | append v => exact hr.elim
  | feed c => exact hr.elim
  | reset => exact hr.elim

theorem chunkFold_append (b : List V) (t u : List (PEv V H)) :
    chunkFold b (t ++ u) = chunkFold (chunkFold b t) u := by
  simp [chunkFold, List.foldl_append]

/-! ## Environments -/

theorem ext_refl (σ : Env H X) : σ.Extends σ := fun _ _ h => h

theorem ext_trans {σ σ' σ'' : Env H X} (h₁ : σ.Extends σ') (h₂ : σ'.Extends σ'') :
    σ.Extends σ'' := fun _ _ h => h₂ (h₁ h)

theorem lookupAll_mono {σ σ' : Env H X} (hσ : σ.Extends σ') :
    ∀ {hs : List H} {ts : List X}, σ.lookupAll hs = some ts → σ'.lookupAll hs = some ts
  | [], ts, h => by simpa [Env.lookupAll] using h
  | h₀ :: hs, ts, h => by
      simp only [Env.lookupAll, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h ⊢
      obtain ⟨x, hx, xs, hxs, rfl⟩ := h
      exact ⟨x, hσ hx, xs, lookupAll_mono hσ (hs := hs) hxs, rfl⟩

theorem built_mono {W : Writer Op X} {σ σ' : Env H X} (hσ : σ.Extends σ') {op : Op}
    {args : List H} {t : X} (h : W.built σ op args = some t) : W.built σ' op args = some t := by
  unfold Writer.built at h ⊢
  rcases hl : σ.lookupAll args with _ | ts
  · simp [hl] at h
  · rw [hl, Option.bind_some] at h
    rw [lookupAll_mono hσ hl, Option.bind_some, h]

variable [DecidableEq H]

/-- **A parsing step moves the chunk buffer by `chunkStep`**, outside undefined behaviour. -/
theorem pstep_buf {ppol : PPolicy H} {σ : Env H X} {s s' : PState V} {e : PEv V H}
    {A : Set (List V × X)} (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) :
    s'.buf = chunkStep s.buf e := by
  cases hs with
  | ret _ hR _ => exact returns_buf hR
  | retBadIgnore _ hR _ _ => exact returns_buf hR
  | retBadSessionTrap _ hR _ _ => have := returns_buf hR; exact this
  | retBadUB _ hR _ _ => have := returns_buf hR; exact this
  | append v => rfl
  | feed c => rfl
  | overrunIgnore hl _ => simp only [chunkStep]; split <;> first | rfl | omega
  | overrunUB hl _ => simp only [chunkStep]; split <;> first | rfl | omega
  | reset => rfl
  | chaos _ h => exact absurd h hc

theorem pstep_noChaos {ppol : PPolicy H} (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub) {σ : Env H X} {s s' : PState V} {e : PEv V H}
    {A : Set (List V × X)} (hs : PStep ppol σ s e s' A) (hc : s.phase ≠ .chaos) :
    s'.phase ≠ .chaos := by
  cases hs with
  | ret _ hR _ => rw [returns_phase hR]; exact hc
  | retBadIgnore _ hR _ _ => rw [returns_phase hR]; exact hc
  | retBadSessionTrap => simp
  | retBadUB _ _ _ h => exact absurd h hb
  | overrunUB _ h => exact absurd h ho
  | chaos _ h => exact absurd h hc
  | _ => simp

/-! ## Runs of the store semantics -/

variable {W : Writer Op X} {pol : Policy H} {ppol : PPolicy H}

theorem wstep_noChaos (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s s' : WState H X}
    {e : WEv Op H} {A : Set X} (hs : WStep W pol none s e s' A) (hc : s.phase ≠ .chaos) :
    s'.phase ≠ .chaos := by
  cases hs with
  | writeChaos _ hu _ => exact absurd hu hw
  | acceptChaos _ hu _ => exact absurd hu ha
  | chaos => exact absurd rfl hc
  | _ => simp

theorem mstep_noChaos (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {s s' : MState V H X}
    {e : MEv Op V H} {A : Set (List V × X)} (hs : MStep W pol ppol none s e s' A)
    (hc : s.ws.phase ≠ .chaos) : s'.ws.phase ≠ .chaos := by
  cases hs with
  | w hw' => exact wstep_noChaos hw ha hw' hc
  | p => exact hc
  | pChaos h => exact absurd h hc

theorem mstep_extends {s s' : MState V H X} {e : MEv Op V H} {A : Set (List V × X)}
    (hs : MStep W pol ppol none s e s' A) : s.ws.store.Extends s'.ws.store :=
  run_store_extends (Host.Run.single (h := mixed W pol ppol none) hs)

/-- What a step accepts without undefined behaviour. -/
theorem mstep_acc (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {s s' : MState V H X}
    {e : MEv Op V H} {A : Set (List V × X)} (hs : MStep W pol ppol none s e s' A)
    (hc : s.ws.phase ≠ .chaos) (hpc : s.ps.phase ≠ .chaos) {q : List V × X} (hq : q ∈ A) :
    ∃ pe, e = .p pe ∧ ∃ w h ps', Returns ppol s.ps pe w h ps' ∧ q.1 = w ∧ h ≠ ppol.sentinel ∧
      s.ws.store h = some q.2 := by
  cases hs with
  | w hw' => exact absurd hq (wstep_noChaos hw ha hw' hc)
  | pChaos h => exact absurd h hc
  | @p ws ps ps' pe A _ hp =>
      refine ⟨pe, rfl, ?_⟩
      cases hp with
      | @ret _ s' _ w h _ _ hR hres =>
          refine ⟨w, h, _, hR, ?_⟩
          unfold resolve at hres
          split_ifs at hres with hh
          · cases hres; simp at hq
          · rcases hx : ws.store h with _ | x
            · simp [hx] at hres
            · simp only [hx, Option.map_some, Option.some.injEq] at hres
              subst hres
              rw [Set.mem_singleton_iff] at hq
              subst hq
              exact ⟨rfl, hh, rfl⟩
      | retBadUB _ _ _ h => exact absurd h hb
      | overrunUB _ h => exact absurd h ho
      | chaos _ h => exact absurd h hpc
      | _ => simp at hq

/-- Writes agree with every extension of the final store, along a run without undefined
behaviour. -/
theorem run_writes (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {σ : Env H X}
    {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol none).Run s t s' A) (hc : s.ws.phase ≠ .chaos)
    (hσ : s'.ws.store.Extends σ) :
    ∀ op args r, MEv.w (.write op args r) ∈ t → WriteAgrees W pol.sentinel σ op args r := by
  induction hr with
  | nil => intro _ _ _ h; simp at h
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have h₁ : s₁.ws.store.Extends σ := ext_trans (run_store_extends hrest) hσ
      intro op args r hm
      rcases List.mem_cons.1 hm with rfl | hm
      · cases hs with
        | w hw' =>
            cases hw' with
            | writeOk hb hf hag =>
                exact .inr ⟨_, built_mono h₁ (built_mono (Handle.Run.store_extends
                  (Host.Run.single (h := writer W pol none) (WStep.writeOk hb hf hag))) hb),
                  h₁ (by simp)⟩
            | writeFail hs _ => exact .inl hs
            | writeChaos _ hu _ => exact absurd hu hw
            | writeFixed _ _ hf => cases hf
            | chaos => exact absurd rfl hc
      · exact ih (mstep_noChaos hw ha hs hc) hσ op args r hm

/-- **Assume/guarantee along the chunk buffer, on one run.** -/
theorem run_subset_chunk (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {σ : Env H X}
    {R : Set (List V × X)} {s s' : MState V H X} {t : List (MEv Op V H)} {A : Set (List V × X)}
    (hr : (mixed W pol ppol none).Run s t s' A) (hc : s.ws.phase ≠ .chaos)
    (hpc : s.ps.phase ≠ .chaos) (hσ : s'.ws.store.Extends σ)
    (hAG : ∀ u e v, t = u ++ .p e :: v → ∀ ps w h ps',
      ps.buf = chunkFold s.ps.buf (parseEvents u) → Returns ppol ps e w h ps' →
      h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R) : A ⊆ R := by
  induction hr with
  | nil => exact Set.empty_subset _
  | @cons s₀ s₁ s₂ e es A' B' hs hrest ih =>
      have hc₁ := mstep_noChaos hw ha hs hc
      have hpc₁ : s₁.ps.phase ≠ .chaos := by
        cases hs with
        | w => exact hpc
        | p _ hp => exact pstep_noChaos hb ho hp hpc
        | pChaos h => exact absurd h hc
      refine Set.union_subset (fun q hq => ?_) (ih hc₁ hpc₁ hσ fun u e' v he => ?_)
      · obtain ⟨pe, rfl, w, h, ps', hR, hw', hh, hx⟩ := mstep_acc hw ha hb ho hs hc hpc hq
        have hx' := hσ (run_store_extends hrest (mstep_extends hs hx))
        have := hAG [] pe es rfl s₀.ps w h ps' (by simp [chunkFold, parseEvents]) hR hh q.2 hx'
        rw [← hw'] at this
        exact this
      · intro ps w h ps' hps
        refine hAG (e :: u) e' v (by rw [he]; rfl) ps w h ps' ?_
        rw [hps]
        cases hs with
        | w => rfl
        | @p ws ps₀ ps₁ pe C hl hp =>
            have := pstep_buf hp hpc
            simp only at this ⊢
            rw [this]
            rfl
        | pChaos h => exact absurd h hc

/-- **Assume/guarantee along the chunk buffer**, store semantics without undefined behaviour. -/
theorem mixedRel_subset_of_chunkAG (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub)
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {T : Set (List (MEv Op V H))}
    {R : Set (List V × X)}
    (hAG : ∀ t ∈ T, ∀ σ, WritesAgree W pol.sentinel σ t → ∀ u e v, t = u ++ .p e :: v →
      ∀ ps w h ps', ps.buf = chunkFold [] (parseEvents u) → Returns ppol ps e w h ps' →
        h ≠ ppol.sentinel → ∀ x, σ h = some x → (w, x) ∈ R) :
    mixedRel W pol ppol T ⊆ R := by
  intro q hq
  obtain ⟨t, ht, s, A, hr, hqA⟩ := Host.mem_lang.1 hq
  have hσ := ext_refl s.ws.store
  have hc : (mixed (V := V) W pol ppol).init.ws.phase ≠ .chaos := by
    simp [mixed, MState.init, WState.init]
  exact run_subset_chunk hw ha hb ho hr hc (by simp [mixed, MState.init, PState.init]) hσ
    (hAG t ht _ (fun op args r hm => run_writes hw ha hr hc hσ op args r hm)) hqA

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ChunkAG
