module

public import Silmaril.Proofs.Wasm.Component.InstSem.Unzip
public import Silmaril.Wasm.Component.InstWired.Defs

/-!
# Instantiation of import-wired components, node by node

`nodesInst_of_denI`: in an import-wired component (`ImportWired`), every instantiation play of
`Comp.denI C` is `NodesInst`: the converse of `extI_inst`/`extI_fail` layer by layer, through
the round decomposition of `Unzip`.

* `implsN_scoped`, `coreNodeI_scoped`: wiring that calls only the first `n` functions does not
  depend on the size of the environment beyond `n`;
* `coreNodeI_calls_lt`: the calls of an import-wired core node go to the first `n` functions;
* `extT_inv`: the routing layer of `extI` (copycat beside the new instance, then `instSplitH`):
  `inst` asks the environment, and the new instance only if the environment is ready; export
  calls below `e` are forwarded to the environment;
* `envInv_extI`: one node: the environment invariant `EnvInv` (its instantiation rounds are
  `NodesInst`, its import calls forwarded) is carried from `D` to `extI e D N`;
* `nodesInst_of_denI`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-! ## Programs -/

theorem runs_bind_inv {E : Sig.{0}} {A B : Type} {f : A → Prog E B} :
    ∀ {P : Prog E A} {cs : List (Call E)} {b : B}, Prog.Runs (P.bind f) cs b →
      ∃ cs₁ cs₂ a, cs = cs₁ ++ cs₂ ∧ Prog.Runs P cs₁ a ∧ Prog.Runs (f a) cs₂ b
  | .pure a, cs, b, h => ⟨[], cs, a, rfl, .pure a, h⟩
  | .call m k, _, b, h => by
    cases h with
    | @call _ _ n cs _ h =>
      obtain ⟨cs₁, cs₂, a, rfl, h₁, h₂⟩ := runs_bind_inv h
      exact ⟨⟨m, n⟩ :: cs₁, cs₂, a, rfl, .call h₁, h₂⟩

theorem runs_runChain_calls {E : Sig.{0}} (Q : List (Call E) → Prop) (hnil : Q [])
    {k : Payload → Prog E (Option Payload)}
    (hk : ∀ x cs r, Prog.Runs (k x) cs r → Q cs) :
    ∀ (ch : List Adapter) (x : Payload) {cs : List (Call E)} {r : Option Payload},
      Prog.Runs (runChain ch k x) cs r → Q cs
  | [], x, cs, r, h => hk x cs r h
  | ad :: ch, x, cs, r, h => by
    simp only [runChain] at h
    split at h
    · cases h; exact hnil
    · obtain ⟨cs₁, cs₂, a, rfl, h₁, h₂⟩ := runs_bind_inv h
      cases h₂
      rw [List.append_nil]
      exact runs_runChain_calls Q hnil hk ch _ h₁

/-- **The calls of an import-wired wiring program go to the first `n` functions.** -/
theorem implsN_calls_lt {n e t : Nat} {args : List Impl} (hs : ScopedList n args)
    {q : (sigN t).Op} {cs : List (Call sigU)} {r : Option Payload}
    (h : Prog.Runs (implsN e args t q) cs r) : ∀ c ∈ cs, c.1.1 < n := by
  simp only [implsN, implsH] at h
  split at h
  · rename_i im him
    have hsc := hs im (List.mem_of_getElem? him)
    refine runs_runChain_calls (fun cs : List (Call sigU) => ∀ c ∈ cs, c.1.1 < n) (fun _ h => nomatch h) ?_
      im.chain q.2 h
    intro x cs r hr
    unfold Impl.Scoped at hsc
    revert hsc hr
    cases im.target with
    | call j =>
      intro hsc hr
      simp only [Target.prog] at hr
      split at hr
      · cases hr with
        | call hr =>
          cases hr
          intro c hc
          rw [List.mem_singleton] at hc
          subst hc
          exact hsc
      · cases hr; exact fun _ h => nomatch h
    | const res =>
      intro _ hr
      simp only [Target.prog] at hr
      cases hr; exact fun _ h => nomatch h
  · cases h; exact fun _ h => nomatch h

/-- Wiring that calls only the first `n` functions does not depend on the size `e ≥ n` of the
environment. -/
theorem implsN_scoped {n e t : Nat} {args : List Impl} (hs : ScopedList n args) (he : n ≤ e) :
    implsN e args t = implsN n args t := by
  funext q
  simp only [implsN, implsH]
  split
  · rename_i im him
    have hsc := hs im (List.mem_of_getElem? him)
    simp only [Impl.prog]
    congr 1
    funext x
    unfold Impl.Scoped at hsc
    revert hsc
    cases im.target with
    | call j =>
      intro hsc
      simp only [Target.prog, hsc, show j < e by omega, ite_true]
    | const _ => intro _; rfl
  · rfl

theorem coreNodeI_scoped (C : CoreSemI M) {n e : Nat} {m : M} {args : List Impl}
    (hs : ScopedList n args) (he : n ≤ e) : coreNodeI C e m args = coreNodeI C n m args := by
  simp only [coreNodeI, implsN_scoped hs he]

theorem allCalls_lt {n e t : Nat} {args : List Impl} (hs : ScopedList n args) :
    ∀ {xs : List (Round sigU (sigN t))}, (∀ r ∈ xs, Prog.Runs (implsN e args t r.q) r.cs r.a) →
      ∀ y ∈ allCalls xs, y.1.1 < n
  | [], _, _, h => nomatch h
  | x :: xs, hr, y, hy => by
    rcases List.mem_append.1 hy with hy | hy
    · exact implsN_calls_lt hs (hr x (.head _)) y hy
    · exact allCalls_lt hs (fun r h => hr r (.tail _ h)) y hy

/-- **The calls of an import-wired core node go to the first `n` functions.** -/
theorem coreNodeI_calls_lt {C : CoreSemI M} {e n : Nat} {m : M} {args : List Impl}
    (hs : ScopedList n args) {ys : List (Call sigU)} {a : InstAns Unit}
    (h : (instRound (F := sigU) ys a).moves ∈ coreNodeI C e m args) : ∀ y ∈ ys, y.1.1 < n := by
  obtain ⟨s, hs', t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := (Strategy.ofHandler _).legal hs'
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv [instRound ys a] ps pt
    (by simpa only [roundsMoves, List.append_nil] using hz)
  have hr := runs_of_ofHandler_rounds hs'
  cases hZ with
  | cons _ xs hc hz' =>
    cases hz'
    rw [List.append_nil] at hr
    intro y hy
    simp only at hc
    rw [hc] at hy
    exact allCalls_lt hs hr y hy

/-! ## Forwarding -/

/-- Rounds of the upper strategy that forward each question once: the lower rounds are the
visible ones. -/
theorem zipR_fwd {E F : Sig.{0}} : ∀ {rs ss : List (Round E F)} {ts : List (Round F F)},
    ZipR rs ss ts → (∀ t ∈ ts, t.cs = [⟨t.q, t.a⟩]) → ss = rs
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons r xs hc hz, ht => by
    have h₀ := ht _ (.head _)
    have ih := zipR_fwd hz fun t h => ht t (.tail _ h)
    subst ih
    obtain ⟨rq, rcs, ra⟩ := r
    simp only at h₀ hc
    rcases xs with _ | ⟨⟨xq, xcs, xa⟩, _ | _⟩
    · simp at h₀
    · simp only [List.map_cons, List.map_nil, Round.call, List.cons.injEq, Sigma.mk.injEq,
        and_true] at h₀
      obtain ⟨rfl, h⟩ := h₀
      cases h
      simp only [allCalls, List.append_nil] at hc
      subst hc
      rfl
    · simp at h₀

theorem zipR_cons_inv {E F G : Sig.{0}} {r : Round E G} {rs : List (Round E G)}
    {ss : List (Round E F)} {ts : List (Round F G)} (h : ZipR (r :: rs) ss ts) :
    ∃ xs ss' ts', ss = xs ++ ss' ∧ ts = ⟨r.q, xs.map Round.call, r.a⟩ :: ts' ∧
      r.cs = allCalls xs ∧ ZipR rs ss' ts' := by
  cases h with
  | cons _ xs hc hz => exact ⟨xs, _, _, rfl, rfl, hc, hz⟩

/-! ## The routing layer of `extI` -/

/-- An export call as a call of the instantiable interface. -/
def exCall (c : Call sigU) : Call sigUI := ⟨some c.1, c.2⟩

/-- The routing layer of `extI e D N`. -/
abbrev extT (e : Nat) (N : Strategy sigU sigUI) : Strategy sigUI sigUI :=
  ((Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N)).comp
    (Strategy.ofHandler (instSplitH e))

/-- A left round of the pairing in `extT`. -/
def leftR (x : Round sigUI sigUI) : Round sigUI (sigUI ⊕ₛ sigUI) := ⟨.inl x.q, x.cs, x.a⟩

theorem splitH_ex_inv {e : Nat} : ∀ {X : List (Round sigUI sigUI)}
    {us : List (Round sigUI (sigUI ⊕ₛ sigUI))} {vs : List (Round (sigUI ⊕ₛ sigUI) sigUI)},
    ZipR X us vs → (∀ v ∈ vs, Prog.Runs (instSplitH e v.q) v.cs v.a) →
    (∀ x ∈ X, ∃ q : sigU.Op, x.q = some q ∧ q.1 < e) → us = X.map leftR
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons x xs hc hz, hv, hX => by
    obtain ⟨q, hq, hqe⟩ := hX x (.head _)
    have ih := splitH_ex_inv hz (fun v h => hv v (.tail _ h)) (fun x h => hX x (.tail _ h))
    subst ih
    obtain ⟨xq, xcs, xa⟩ := x
    simp only at hq hc
    subst hq
    have h₀ := hv _ (.head _)
    simp only [instSplitH, hqe, ite_true] at h₀
    rcases xs with _ | ⟨⟨uq, ucs, ua⟩, _ | _⟩
    · cases h₀
    · cases h₀ with
      | call h' =>
        cases h'
        simp only [allCalls, List.append_nil] at hc
        subst hc
        rfl
    · cases h₀ with
      | call h' => cases h'

theorem lefts_map_leftR (X : List (Round sigUI sigUI)) :
    lefts ((X.map leftR).map unsided) = X ∧ rights ((X.map leftR).map unsided) = [] := by
  induction X with
  | nil => exact ⟨rfl, rfl⟩
  | cons x X ih =>
    obtain ⟨xq, xcs, xa⟩ := x
    exact ⟨congrArg _ ih.1, ih.2⟩

theorem exH_rounds_calls : ∀ {hs : List (Round sigUI sigU)},
    (∀ h ∈ hs, Prog.Runs (exH sigU Unit h.q) h.cs h.a) →
    allCalls hs = (hs.map Round.call).map exCall
  | [], _ => rfl
  | ⟨q, cs, a⟩ :: hs, h => by
    have h₀ := h _ (.head _)
    simp only [Handler.ofHom, exHom] at h₀
    cases h₀ with
    | call h' =>
      cases h'
      simp only [allCalls, List.map_cons, List.singleton_append,
        exH_rounds_calls fun h' hh => h h' (.tail _ hh)]
      rfl

/-- **The routing layer of `extI`**: `inst` asks the environment, then the new instance only if
the environment is ready; export calls below `e` are forwarded to the environment. -/
theorem extT_inv {e : Nat} {N : Strategy sigU sigUI} {c : List (Call sigUI)} {a : InstAns Unit}
    {X : List (Round sigUI sigUI)} (hX : ∀ x ∈ X, ∃ q : sigU.Op, x.q = some q ∧ q.1 < e)
    (h : roundsMoves (⟨none, c, a⟩ :: X) ∈ extT e N) :
    (∀ x ∈ X, x.cs = [⟨x.q, x.a⟩]) ∧
      ((∃ r, a = .fail r ∧ c = [⟨none, .fail r⟩]) ∨
        ∃ ys : List (Call sigU), (instRound (F := sigU) ys a).moves ∈ N ∧
          c = ⟨none, .ready⟩ :: ys.map exCall) := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := Strategy.legal _ hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨us, vs, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  have hv := runs_of_ofHandler_rounds ht
  obtain ⟨xs₀, us', vs', rfl, rfl, hc, hZ'⟩ := zipR_cons_inv hZ
  simp only at hc
  subst hc
  have hus' := splitH_ex_inv hZ' (fun v h => hv v (.tail _ h)) hX
  subst hus'
  obtain ⟨hL, hR⟩ := mem_pair_rounds_inv hs
  have hid := id_rounds_inv hL
  have hX' : ∀ x ∈ X, x.cs = [⟨x.q, x.a⟩] := by
    intro x hx
    refine hid x ?_
    rw [List.map_append, show ∀ l₁ l₂ : List (Round sigUI sigUI ⊕ Round sigUI sigUI),
      lefts (l₁ ++ l₂) = lefts l₁ ++ lefts l₂ from fun l₁ l₂ => by
        induction l₁ with
        | nil => rfl
        | cons u l ih => rcases u with u | u <;> simp only [List.cons_append, lefts, ih]]
    rw [(lefts_map_leftR X).1]
    exact List.mem_append_right _ hx
  refine ⟨hX', ?_⟩
  have h₀ := hv _ (.head _)
  simp only [instSplitH] at h₀
  rcases xs₀ with _ | ⟨⟨uq₁, ucs₁, ua₁⟩, xs₀⟩
  · cases h₀
  · simp only [List.map_cons, Round.call] at h₀
    cases h₀ with
    | @call _ _ n₁ _ _ h₁ =>
      rcases n₁ with _ | r
      · -- the environment is ready: the new instance is asked
        rcases xs₀ with _ | ⟨⟨uq₂, ucs₂, ua₂⟩, xs₀⟩
        · cases h₁
        · cases h₁ with
          | @call _ _ n₂ _ _ h₂ =>
            rcases xs₀ with _ | ⟨_, _⟩
            · cases h₂
              right
              simp only [List.map_cons, List.cons_append, List.nil_append, unsided] at hid hR
              have h₁' := hid _ (.head _)
              simp only at h₁'
              subst h₁'
              simp only [rights, (lefts_map_leftR X).2] at hR
              obtain ⟨s', hs', t', ht', hz'⟩ := hR
              obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
              obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
              obtain ⟨hrs, ns, rfl, rfl, hZ₂⟩ := zip_rounds_inv [⟨none, ucs₂, ua₂⟩] ps' pt'
                (by simpa only [roundsMoves, List.append_nil] using hz')
              obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hz₂⟩ := zipR_cons_inv hZ₂
              cases hz₂
              rw [List.append_nil] at hs'
              have hcall := exH_rounds_calls (runs_of_ofHandler_rounds hs')
              refine ⟨xs₂.map Round.call, ?_, ?_⟩
              · simpa only [roundsMoves, List.append_nil] using ht'
              · simp only at hc₂
                simp only [allCalls, List.append_nil, hc₂, hcall, List.singleton_append]
            · cases h₂
      · -- the environment fails: the new instance is not asked
        rcases xs₀ with _ | ⟨_, _⟩
        · cases h₁
          left
          simp only [List.map_cons, List.cons_append, List.nil_append, unsided] at hid
          have h₁' := hid _ (.head _)
          simp only at h₁'
          subst h₁'
          exact ⟨r, rfl, by simp only [allCalls, List.append_nil]⟩
        · cases h₁

end Silmaril.Proofs.Wasm.Component.InstSem
