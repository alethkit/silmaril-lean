module

public import Silmaril.Formats.SExp.Pattern.Defs

/-! # Proofs: patterns, combinators and AST encodings -/

@[expose] public section

namespace Silmaril.Proofs.Formats.SExp.Pattern

open Silmaril.Formats

variable {α β : Type}

theorem mem_pair {L₁ L₂ : Set (SExp α)} {x : SExp α} :
    x ∈ pair L₁ L₂ ↔ ∃ a b, x = SExp.ofList [a, b] ∧ a ∈ L₁ ∧ b ∈ L₂ := by
  constructor
  · rintro ⟨cs, rfl, h⟩
    rcases h with _ | ⟨ha, _ | ⟨hb, h⟩⟩
    cases h
    exact ⟨_, _, rfl, ha, hb⟩
  · rintro ⟨a, b, rfl, ha, hb⟩
    exact ⟨[a, b], rfl, .cons ha (.cons hb .nil)⟩

theorem tuple_inter (Ls Ms : List (Set (SExp α))) (h : Ls.length = Ms.length) :
    tuple (List.zipWith (· ∩ ·) Ls Ms) = tuple Ls ∩ tuple Ms := by
  ext x
  constructor
  · rintro ⟨cs, rfl, hc⟩
    refine ⟨⟨cs, rfl, ?_⟩, ⟨cs, rfl, ?_⟩⟩
    · induction Ls generalizing cs Ms with
      | nil => cases Ms <;> simp_all
      | cons L Ls ih =>
          cases Ms with
          | nil => simp at h
          | cons M Ms =>
              rcases hc with _ | ⟨hm, hc⟩
              exact .cons hm.1 (ih Ms (by simpa using h) _ hc)
    · induction Ls generalizing cs Ms with
      | nil => cases Ms <;> simp_all
      | cons L Ls ih =>
          cases Ms with
          | nil => simp at h
          | cons M Ms =>
              rcases hc with _ | ⟨hm, hc⟩
              exact .cons hm.2 (ih Ms (by simpa using h) _ hc)
  · rintro ⟨⟨cs, rfl, hc⟩, ⟨ds, hd, hd'⟩⟩
    have := SExp.ofList_injective hd
    subst this
    clear hd
    refine ⟨cs, rfl, ?_⟩
    induction cs generalizing Ls Ms with
    | nil => cases hc; cases hd'; exact .nil
    | cons c cs ih =>
        rcases hc with _ | ⟨hL, hc⟩
        rcases hd' with _ | ⟨hM, hd'⟩
        exact .cons ⟨hL, hM⟩ (ih _ _ (by simpa using h) hc hd')

theorem pair_inter_left (L L' M : Set (SExp α)) : pair (L ∩ L') M = pair L M ∩ pair L' M := by
  ext x
  simp only [Set.mem_inter_iff, mem_pair]
  constructor
  · rintro ⟨a, b, rfl, ⟨ha, ha'⟩, hb⟩
    exact ⟨⟨a, b, rfl, ha, hb⟩, ⟨a, b, rfl, ha', hb⟩⟩
  · rintro ⟨⟨a, b, rfl, ha, hb⟩, ⟨a', b', h, ha', -⟩⟩
    have := SExp.ofList_injective h
    simp only [List.cons.injEq] at this
    obtain ⟨rfl, rfl, -⟩ := this
    exact ⟨a, b, rfl, ⟨ha, ha'⟩, hb⟩

theorem pair_union_left (L L' M : Set (SExp α)) : pair (L ∪ L') M = pair L M ∪ pair L' M := by
  ext x
  simp only [Set.mem_union, mem_pair]
  constructor
  · rintro ⟨a, b, rfl, ha | ha, hb⟩
    · exact .inl ⟨a, b, rfl, ha, hb⟩
    · exact .inr ⟨a, b, rfl, ha, hb⟩
  · rintro (⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩)
    · exact ⟨a, b, rfl, .inl ha, hb⟩
    · exact ⟨a, b, rfl, .inr ha, hb⟩

theorem tuple_subset_star (L : Set (SExp α)) (Ls : List (Set (SExp α))) (h : ∀ M ∈ Ls, M ⊆ L) :
    tuple Ls ⊆ star L := by
  rintro x ⟨cs, rfl, hc⟩
  refine ⟨cs, rfl, ?_⟩
  induction hc with
  | nil => simp
  | cons hm _ ih =>
      intro c hcm
      rcases List.mem_cons.1 hcm with rfl | hcm
      · exact h _ List.mem_cons_self hm
      · exact ih (fun M hM => h M (List.mem_cons_of_mem _ hM)) c hcm

theorem pat_lang_ground : ∀ e : SExp α, Pat.lang (Pat.ground e) = {e} := by
  intro e
  induction e with
  | atom a => rfl
  | list n cs ih =>
      ext x
      simp only [Pat.ground, SExp.map, Pat.lang, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ds, rfl, h⟩
        congr 1
        funext i
        have := h i
        simp only [Pat.ground] at ih
        rw [ih i] at this
        exact this
      · rintro rfl
        refine ⟨cs, rfl, fun i => ?_⟩
        simp only [Pat.ground] at ih
        rw [ih i]; rfl

/-- Widening holes widens the language. -/
theorem pat_lang_mono {f : Set (SExp α) → Set (SExp α)} (hf : ∀ L, L ⊆ f L) :
    ∀ p : Pat α, Pat.lang p ⊆ Pat.lang (p.map (Sum.map id f)) := by
  intro p
  induction p with
  | atom a =>
      rcases a with a | L
      · exact le_rfl
      · exact hf L
  | list n ps ih =>
      rintro x ⟨cs, rfl, h⟩
      exact ⟨cs, rfl, fun i => ih i (h i)⟩

theorem encode_injective {S : Sig} {tagEnc : S.Tag → SExp β} {argEnc : ∀ t, S.Arg t → List (SExp β)}
    (ht : Function.Injective tagEnc) (ha : ∀ t, Function.Injective (argEnc t))
    (hl : AST.ArgLenFixed argEnc) : Function.Injective (AST.encode tagEnc argEnc) := by
  intro x
  induction x with
  | atom e => exact e.elim
  | tag v n cs ih =>
      intro y hxy
      cases y with
      | atom e => exact e.elim
      | tag w m ds =>
          obtain ⟨t, a⟩ := v
          obtain ⟨t', a'⟩ := w
          simp only [AST.encode, AST.encodeWith] at hxy
          have h1 := SExp.ofList_injective hxy
          simp only [List.cons_append, List.cons.injEq] at h1
          obtain ⟨htt, hrest⟩ := h1
          have := ht htt
          subst this
          obtain ⟨haa, hcs⟩ := List.append_inj hrest (hl t a a')
          have := ha t haa
          subst this
          have hnm : n = m := by simpa using congrArg List.length hcs
          subst hnm
          congr 1
          funext i
          apply ih i
          have := congrArg (fun l => l[i]?) hcs
          simpa [AST.encode] using this

end Silmaril.Proofs.Formats.SExp.Pattern
