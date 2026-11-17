module

public import Silmaril.Proofs.Wasm.Component.InstSem.WiredEngine
public import Silmaril.Proofs.Wasm.Component.InstSem.Export

/-!
# An export call after the instantiation of import-wired nodes

The converse of `InstSem.Export` for one export call without calls below, after a ready
instantiation:

* `coreNodeI_ex_inv`: a core node's instantiation round followed by one export round is its
  module's, the module's import calls answered by the wiring (`implsN`), the export question
  in range (`widenH`) unless the answer is a trap;
* `extT_inv_right`: the routing layer of `extI` sends an export call at or past `e` to the new
  instance, shifted;
* `EnvInvE`, `envInvE_denNodesI`: **the environment after the nodes `pre`**: an instantiation
  round, forwarded import calls and one export round without calls below are the nodes'
  instantiations followed by that export round at the node owning the export (no import is
  owned: an import call is forwarded, so makes a call below);
* `denI_ex_inv`: on top, the component's export runs its program.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-! ## A core node -/

/-- **A core node's instantiation round and one export round are its module's**, the module's
import calls answered by the wiring; the export is in range unless it is answered by a trap. -/
theorem coreNodeI_ex_inv {C : CoreSemI M} {e : Nat} {m : M} {args : List Impl}
    {w cs : List (Call sigU)} {a : InstAns Unit} {q : sigU.Op} {n : Option Payload}
    (h : roundsMoves [instRound (F := sigU) w a, exRound (R := Unit) (⟨q, cs, n⟩ : Round sigU sigU)] ∈
      coreNodeI C e m args) :
    ∃ xs₁ xs₂ : List (Round sigU (sigN (CoreModule.imports m).length)),
      (∀ y ∈ xs₁ ++ xs₂, Prog.Runs (implsN e args (CoreModule.imports m).length y.q) y.cs y.a) ∧
      w = allCalls xs₁ ∧ cs = allCalls xs₂ ∧
      ((n = none ∧ xs₂ = []) ∨ ∃ hq : q.1 < (CoreModule.exports m).length,
        roundsMoves [instRound (F := CoreIface.sig (CoreModule.exports m)) (xs₁.map Round.call) a,
          exRound (R := Unit) (⟨(⟨q.1, hq⟩, q.2), xs₂.map Round.call, n⟩ :
            Round (sigN (CoreModule.imports m).length) (CoreIface.sig (CoreModule.exports m)))] ∈
          C.sem m) := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := (Strategy.ofHandler _).legal hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  obtain ⟨xs₁, _, _, rfl, rfl, hc₁, hZ₁⟩ := zipR_cons_inv hZ
  obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hZ₂⟩ := zipR_cons_inv hZ₁
  cases hZ₂
  rw [List.append_nil] at hs
  simp only [exRound] at hc₁ hc₂
  refine ⟨xs₁, xs₂, runs_of_ofHandler_rounds hs, hc₁, hc₂, ?_⟩
  obtain ⟨s', hs', t', ht', hz'⟩ := ht
  obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
  obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
  obtain ⟨us, vs, rfl, rfl, hZ'⟩ := zip_rounds_inv _ ps' pt' hz'
  obtain ⟨us₁, _, _, rfl, rfl, hd₁, hZ'₁⟩ := zipR_cons_inv hZ'
  obtain ⟨us₂, _, _, rfl, rfl, hd₂, hZ'₂⟩ := zipR_cons_inv hZ'₁
  cases hZ'₂
  rw [List.append_nil] at hs'
  have hr := runs_of_ofHandler_rounds ht'
  have h₁ := hr _ (.head _)
  have h₂ := hr _ (.tail _ (.head _))
  simp only [liftH, exRound, instRound] at h₁ h₂
  simp only at hd₁ hd₂
  -- the instantiation round is forwarded
  rcases us₁ with _ | ⟨⟨uq, ucs, ua⟩, _ | _⟩
  · cases h₁
  · cases h₁ with
    | call h₁ =>
      cases h₁
      simp only [allCalls, List.append_nil] at hd₁
      subst hd₁
      -- the export round
      obtain ⟨k, pl⟩ := q
      simp only [widenH] at h₂
      by_cases hk : k < (CoreModule.exports m).length
      · simp only [hk, ↓reduceDIte, Prog.interp] at h₂
        rcases us₂ with _ | ⟨⟨vq, vcs, va⟩, _ | _⟩
        · cases h₂
        · cases h₂ with
          | call h₂ =>
            cases h₂
            simp only [allCalls, List.append_nil] at hd₂
            subst hd₂
            refine .inr ⟨hk, ?_⟩
            simp only [roundsMoves, List.append_nil, List.singleton_append] at hs' ⊢
            exact hs'
        · cases h₂ with
          | call h₂ => cases h₂
      · simp only [hk, ↓reduceDIte, Prog.interp] at h₂
        rcases us₂ with _ | ⟨_, _⟩
        · cases h₂
          refine .inl ⟨rfl, ?_⟩
          cases xs₂ with
          | nil => rfl
          | cons x xs => simp [allCalls] at hd₂
        · cases h₂
  · cases h₁ with
    | call h₁ => cases h₁

/-! ## The routing layer -/

theorem zipR_append_inv {E F G : Sig.{0}} :
    ∀ {rs₁ rs₂ : List (Round E G)} {ss : List (Round E F)} {ts : List (Round F G)},
      ZipR (rs₁ ++ rs₂) ss ts →
      ∃ ss₁ ss₂ ts₁ ts₂, ss = ss₁ ++ ss₂ ∧ ts = ts₁ ++ ts₂ ∧ ZipR rs₁ ss₁ ts₁ ∧ ZipR rs₂ ss₂ ts₂
  | [], _, _, _, h => ⟨[], _, [], _, rfl, rfl, .nil, h⟩
  | r :: rs₁, rs₂, _, _, h => by
    obtain ⟨xs, ss', ts', rfl, rfl, hc, hz⟩ := zipR_cons_inv (rs := rs₁ ++ rs₂) h
    obtain ⟨ss₁, ss₂, ts₁, ts₂, rfl, rfl, h₁, h₂⟩ := zipR_append_inv hz
    exact ⟨xs ++ ss₁, ss₂, _ :: ts₁, ts₂, by rw [List.append_assoc], rfl, .cons r xs hc h₁, h₂⟩

theorem lefts_append {E F₁ F₂ : Sig.{0}} :
    ∀ l₁ l₂ : List (Round E F₁ ⊕ Round E F₂), lefts (l₁ ++ l₂) = lefts l₁ ++ lefts l₂
  | [], _ => rfl
  | .inl _ :: l, l₂ => by simp only [List.cons_append, lefts, lefts_append l l₂]
  | .inr _ :: l, l₂ => by simp only [List.cons_append, lefts, lefts_append l l₂]

theorem rights_append {E F₁ F₂ : Sig.{0}} :
    ∀ l₁ l₂ : List (Round E F₁ ⊕ Round E F₂), rights (l₁ ++ l₂) = rights l₁ ++ rights l₂
  | [], _ => rfl
  | .inl _ :: l, l₂ => by simp only [List.cons_append, rights, rights_append l l₂]
  | .inr _ :: l, l₂ => by simp only [List.cons_append, rights, rights_append l l₂]

/-- **The routing layer of `extI`, an export call at or past `e`**: after a ready instantiation
and export calls below `e` (forwarded to the environment), an export call at or past `e` is the
new instance's, shifted by `e`, its calls made export calls below. -/
theorem extT_inv_right {e : Nat} {N : Strategy sigU sigUI} {c c₂ : List (Call sigUI)}
    {X : List (Round sigUI sigUI)} {q : sigU.Op} {n : Option Payload}
    (hX : ∀ x ∈ X, ∃ q : sigU.Op, x.q = some q ∧ q.1 < e) (hq : e ≤ q.1)
    (h : roundsMoves (⟨none, c, .ready⟩ :: X ++ [⟨some q, c₂, n⟩]) ∈ extT e N) :
    (∀ x ∈ X, x.cs = [⟨x.q, x.a⟩]) ∧
      ∃ ys ys₂ : List (Call sigU),
        roundsMoves [instRound (F := sigU) ys .ready,
          exRound (R := Unit) (⟨(q.1 - e, q.2), ys₂, n⟩ : Round sigU sigU)] ∈ N ∧
        c = ⟨none, .ready⟩ :: ys.map exCall ∧ c₂ = ys₂.map exCall := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := Strategy.legal _ hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨us, vs, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  have hv := runs_of_ofHandler_rounds ht
  obtain ⟨xs₀, us', vs', rfl, rfl, hc, hZ'⟩ := zipR_cons_inv hZ
  obtain ⟨uX, uf, vX, vf, rfl, rfl, hZX, hZf⟩ := zipR_append_inv hZ'
  obtain ⟨xf, _, _, rfl, rfl, hcf, hZf'⟩ := zipR_cons_inv hZf
  cases hZf'
  simp only at hc hcf
  subst hc hcf
  have hvX : ∀ v ∈ vX, Prog.Runs (instSplitH e v.q) v.cs v.a :=
    fun v h => hv v (.tail _ (List.mem_append_left _ h))
  have huX := splitH_ex_inv hZX hvX hX
  subst huX
  -- the final round goes right
  have hf := hv _ (.tail _ (List.mem_append_right _ (.head _)))
  have hqe : ¬ q.1 < e := by omega
  simp only [instSplitH, hqe, ↓reduceIte] at hf
  rcases xf with _ | ⟨⟨fq, fcs, fa⟩, _ | _⟩
  · cases hf
  · cases hf with
    | call hf' =>
      cases hf'
      -- the instantiation round
      have h₀ := hv _ (.head _)
      simp only [instSplitH] at h₀
      rcases xs₀ with _ | ⟨⟨uq₁, ucs₁, ua₁⟩, xs₀⟩
      · cases h₀
      · simp only [List.map_cons, Round.call] at h₀
        cases h₀ with
        | @call _ _ n₁ _ _ h₁ =>
          rcases n₁ with _ | r
          · rcases xs₀ with _ | ⟨⟨uq₂, ucs₂, ua₂⟩, xs₀⟩
            · cases h₁
            · cases h₁ with
              | @call _ _ n₂ _ _ h₂ =>
                rcases xs₀ with _ | ⟨_, _⟩
                · cases h₂
                  obtain ⟨hL, hR⟩ := mem_pair_rounds_inv hs
                  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
                    List.nil_append, unsided] at hL hR
                  simp only [lefts, rights, lefts_append, rights_append, (lefts_map_leftR X).1,
                    (lefts_map_leftR X).2, List.nil_append] at hL hR
                  have hid := id_rounds_inv hL
                  refine ⟨fun x hx => hid x (.tail _ (List.mem_append_left _ hx)), ?_⟩
                  obtain ⟨s', hs', t', ht', hz'⟩ := hR
                  obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
                  obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
                  obtain ⟨hrs, ns, rfl, rfl, hZ₂⟩ := zip_rounds_inv
                    [(⟨none, ucs₂, InstAns.ready⟩ : Round sigUI sigUI), ⟨some (q.1 - e, q.2), fcs, fa⟩] ps' pt' hz'
                  obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hz₂⟩ := zipR_cons_inv hZ₂
                  obtain ⟨xs₃, _, _, rfl, rfl, hc₃, hz₃⟩ := zipR_cons_inv hz₂
                  cases hz₃
                  rw [List.append_nil] at hs'
                  have hrun := runs_of_ofHandler_rounds hs'
                  have hcall₂ := exH_rounds_calls fun h hh => hrun h (List.mem_append_left _ hh)
                  have hcall₃ := exH_rounds_calls fun h hh => hrun h (List.mem_append_right _ hh)
                  simp only at hc₂ hc₃
                  refine ⟨xs₂.map Round.call, xs₃.map Round.call, ?_, ?_, ?_⟩
                  · simpa only [roundsMoves, List.append_nil, instRound, exRound] using ht'
                  · have h₁' := hid _ (.head _)
                    simp only at h₁'
                    simp only [allCalls, List.append_nil, hc₂, hcall₂, h₁', List.singleton_append]
                  · simp only [allCalls, List.append_nil, hc₃, hcall₃]
                · cases h₂
          · rcases xs₀ with _ | ⟨_, _⟩
            · cases h₁
            · cases h₁
  · cases hf with
    | call hf' => cases hf'

end Silmaril.Proofs.Wasm.Component.InstSem
