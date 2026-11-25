module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Thms

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs

universe u

variable {g : Graph.{u}} {x y : Value.{u}}

theorem mem_domain : g.domain.mem x ↔ ∃ y, g.relates x y := by
  rw [SetData.mem, Graph.domain, ZFSet.mem_sep]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  obtain ⟨y, hy⟩ := h
  have hx : ({x.code} : ZFSet) ∈ g.pairs.sUnion :=
    ZFSet.mem_sUnion.mpr ⟨_, hy, ZFSet.mem_pair.mpr (.inl rfl)⟩
  exact ZFSet.mem_sUnion.mpr ⟨_, hx, ZFSet.mem_singleton.mpr rfl⟩

theorem lookup_eq_some : g.lookup x = some y ↔ g.relates x y := by
  classical
  by_cases h : ∃ z, g.relates x z
  · rw [Graph.lookup, dite_eq_left h, Option.some.injEq]
    exact ⟨fun e => e ▸ Classical.choose_spec h, fun hy =>
      Value.code_injective (g.single_valued (Classical.choose_spec h) hy)⟩
  · exact iff_of_false (by simp [Graph.lookup, h]) (fun hy => h ⟨y, hy⟩)

theorem relates_ofFn {s : SetData.{u}} {f : Value.{u} → Value.{u}} :
    (Graph.ofFn s f).relates x y ↔ s.mem x ∧ f x = y := by
  refine ZFSet.mem_range.trans ⟨?_, fun ⟨hx, hy⟩ => ⟨⟨x.code, hx⟩, congrArg (ZFSet.pair x.code)
    (congrArg Value.code hy)⟩⟩
  rintro ⟨⟨k, hk⟩, he⟩
  obtain ⟨rfl, he⟩ := ZFSet.pair_inj.mp he
  exact ⟨hk, Value.code_injective he⟩

theorem graph_eq_of_relates {g h : Graph.{u}} (he : ∀ x y, g.relates x y ↔ h.relates x y) :
    g = h := by
  suffices hpair : g.pairs = h.pairs by
    cases g; cases h; cases hpair; rfl
  apply ZFSet.ext
  intro p
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨x, y, rfl⟩ := g.pair_form p hp
    exact (he ⟨x⟩ ⟨y⟩).mp hp
  · obtain ⟨x, y, rfl⟩ := h.pair_form p hp
    exact (he ⟨x⟩ ⟨y⟩).mpr hp

open Graph in
section

variable {h : Graph.{u}}

theorem lookup_eq_none : g.lookup x = none ↔ ¬ g.domain.mem x := by
  classical
  by_cases h : ∃ y, g.relates x y <;> simp [lookup, mem_domain, h]

theorem ext_of_domain_lookup (hd : g.domain = h.domain)
    (he : ∀ x, g.domain.mem x → g.lookup x = h.lookup x) : g = h := by
  classical
  apply graph_eq_of_relates
  intro x y
  rw [← lookup_eq_some, ← lookup_eq_some]
  by_cases hx : g.domain.mem x
  · rw [he x hx]
  · rw [lookup_eq_none.mpr hx, lookup_eq_none.mpr (hd ▸ hx)]

@[simp] theorem domain_ofFn (s : SetData.{u}) (f : Value.{u} → Value.{u}) :
    (ofFn s f).domain = s :=
  SetData.ext fun _ => by simp [mem_domain, relates_ofFn]

theorem lookup_ofFn {s : SetData.{u}} {f : Value.{u} → Value.{u}} (hx : s.mem x) :
    (ofFn s f).lookup x = some (f x) :=
  lookup_eq_some.mpr (relates_ofFn.mpr ⟨hx, rfl⟩)

theorem update_missing (hx : ¬ g.domain.mem x) : g.update x y = g := by
  simp [update, hx]

@[simp] theorem domain_update (g : Graph.{u}) (x y : Value.{u}) : (g.update x y).domain = g.domain := by
  classical
  by_cases hx : g.domain.mem x <;> simp [update, hx]

theorem lookup_update_other {k : Value.{u}} (hne : k ≠ x) :
    (g.update x y).lookup k = g.lookup k := by
  classical
  by_cases hx : g.domain.mem x
  · by_cases hk : g.domain.mem k
    · rw [update, ite_eq_left hx, lookup_ofFn hk, ite_eq_right hne]
      cases h : g.lookup k with
      | none => exact False.elim (lookup_eq_none.mp h hk)
      | some v => rfl
    · rw [lookup_eq_none.mpr (by simpa using hk), lookup_eq_none.mpr hk]
  · rw [update_missing hx]

end

theorem isFunc_iff {s t : SetData.{u}} :
    ZFSet.IsFunc s.codes t.codes g.pairs ↔ g.domain = s ∧
      ∀ x y, g.relates x y → t.mem y := by
  constructor
  · intro ⟨hsub, happ⟩
    refine ⟨SetData.ext fun x => mem_domain.trans ⟨?_, ?_⟩, fun x y h =>
      (ZFSet.pair_mem_prod.mp (hsub h)).2⟩
    · exact fun ⟨y, hy⟩ => (ZFSet.pair_mem_prod.mp (hsub hy)).1
    · exact fun hx => let ⟨y, hy, _⟩ := happ x.code hx; ⟨⟨y⟩, hy⟩
  · intro ⟨hd, hr⟩
    refine ⟨fun p hp => ?_, fun x hx => ?_⟩
    · obtain ⟨x, y, rfl⟩ := g.pair_form p hp
      have hx : g.domain.mem ⟨x⟩ := mem_domain.mpr ⟨⟨y⟩, hp⟩
      exact ZFSet.pair_mem_prod.mpr ⟨hd ▸ hx, hr ⟨x⟩ ⟨y⟩ hp⟩
    · have hx' : g.domain.mem ⟨x⟩ := hd.symm ▸ hx
      obtain ⟨y, hy⟩ := mem_domain.mp hx'
      exact ⟨y.code, hy, fun _ hz => g.single_valued hz hy⟩

theorem mem_functionSet {s t : SetData.{u}} {v : Value.{u}} :
    (s.functionSet t).mem v ↔ ∃ g : Graph.{u}, Value.function g = v ∧ g.domain = s ∧
      ∀ x y, g.relates x y → t.mem y := by
  refine ZFSet.mem_range.trans ⟨?_, ?_⟩
  · rintro ⟨⟨p, hp⟩, hv⟩
    have hf := ZFSet.mem_funs.mp hp
    let g : Graph :=
      ⟨p, fun _ hm => let ⟨x, _, y, _, he⟩ := ZFSet.mem_prod.mp (hf.1 hm); ⟨x, y, he.symm⟩,
        fun {_ _ _} hy hz =>
          let ⟨_, _, hu⟩ := hf.2 _ (ZFSet.pair_mem_prod.mp (hf.1 hy)).1
          (hu _ hy).trans (hu _ hz).symm⟩
    exact ⟨g, Value.code_injective hv, isFunc_iff.mp (show ZFSet.IsFunc _ _ g.pairs from hf)⟩
  · rintro ⟨g, rfl, hd, hr⟩
    exact ⟨⟨g.pairs, ZFSet.mem_funs.mpr (isFunc_iff.mpr ⟨hd, hr⟩)⟩, rfl⟩

end Silmaril.Logic.Temporal.TLA.Data.Tagged.Proofs
