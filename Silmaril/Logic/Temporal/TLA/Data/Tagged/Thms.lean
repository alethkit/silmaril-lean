module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Defs
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Sets

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u v

theorem natCode_injective : Function.Injective (natCode.{u}) :=
  Proofs.natCode_injective

theorem Kind.index_injective : Function.Injective Kind.index := by
  intro a b h
  cases a <;> cases b <;> simp_all [Kind.index]

theorem Value.code_injective : Function.Injective (Value.code.{u}) := by
  intro a b h
  cases a; cases b; cases h; rfl

theorem SetData.codes_injective : Function.Injective (SetData.codes.{u}) := by
  intro a b h
  cases a; cases b; cases h; rfl

theorem Value.tagged_inj {k l : Kind} {a b : ZFSet.{u}} :
    tagged k a = tagged l b ↔ k = l ∧ a = b := by
  refine ⟨fun h => ?_, fun ⟨hk, hab⟩ => hk ▸ hab ▸ rfl⟩
  exact (ZFSet.pair_inj.mp (congrArg Value.code h)).imp (fun h => Kind.index_injective (natCode_injective h)) id

theorem Value.set_injective : Function.Injective (Value.set.{u}) :=
  fun _ _ h => SetData.codes_injective (Value.tagged_inj.mp h).2

theorem decode_eq_some {A : Type u} {B : Type v} {f : A → B} (hf : Function.Injective f)
    {b : B} {a : A} : decode f b = some a ↔ f a = b :=
  Proofs.decode_eq_some hf

theorem decode_eq_none {A : Type u} {B : Type v} {f : A → B} {b : B}
    (h : ¬ ∃ a, f a = b) : decode f b = none := by
  classical
  simp [decode, h]

theorem Value.asSet_eq_some {v : Value.{u}} {s : SetData.{u}} :
    v.asSet = some s ↔ set s = v :=
  decode_eq_some set_injective

@[simp] theorem Value.asSet_set (s : SetData.{u}) : (set s).asSet = some s :=
  asSet_eq_some.mpr rfl

@[simp] theorem Value.mem_set {x : Value.{u}} {s : SetData.{u}} : x.mem (.set s) ↔ s.mem x :=
  ⟨fun ⟨_, e, h⟩ => Value.set_injective e ▸ h, fun h => ⟨s, rfl, h⟩⟩

theorem Value.not_mem_of_asSet_none {x s : Value.{u}} (h : s.asSet = none) : ¬ x.mem s :=
  fun ⟨_, ht, _⟩ => Option.some_ne_none _ ((asSet_eq_some.mpr ht).symm.trans h)

theorem SetData.exists_not_mem (s : SetData.{u}) : ∃ x, ¬ s.mem x :=
  ⟨⟨s.codes⟩, ZFSet.mem_irrefl _⟩

theorem SetData.ext {s t : SetData.{u}} (h : ∀ x, s.mem x ↔ t.mem x) : s = t :=
  codes_injective (ZFSet.ext fun x => h ⟨x⟩)

theorem Value.set_eq_iff {s t : SetData.{u}} : set s = set t ↔ ∀ x : Value.{u}, x.mem (set s) ↔ x.mem (set t) :=
  ⟨fun h => h ▸ fun _ => Iff.rfl, fun h => congrArg set (SetData.ext fun x => by simpa using h x)⟩

@[simp] theorem SetData.mem_enum (x : Value.{u}) (xs : List Value.{u}) :
    (enum xs).mem x ↔ x ∈ xs :=
  Proofs.mem_enum x xs

@[simp] theorem SetData.mem_sep {s : SetData.{u}} {p : Value.{u} → Prop} {x : Value.{u}} :
    (s.sep p).mem x ↔ s.mem x ∧ p x := by
  cases x
  exact ZFSet.mem_sep (p := fun c => p ⟨c⟩)

theorem SetData.mem_image {s : SetData.{u}} {f : Value.{u} → Value.{u}} {x : Value.{u}} :
    (s.image f).mem x ↔ ∃ y, s.mem y ∧ f y = x := by
  exact ZFSet.mem_range.trans ⟨fun ⟨⟨y, hy⟩, h⟩ => ⟨⟨y⟩, hy, Value.code_injective h⟩,
    fun ⟨y, hy, h⟩ => ⟨⟨y.code, hy⟩, congrArg Value.code h⟩⟩

theorem SetData.mem_powerset {s : SetData.{u}} {x : Value.{u}} :
    s.powerset.mem x ↔ ∃ t : SetData.{u}, Value.set t = x ∧ t.subset s := by
  refine ZFSet.mem_range.trans ⟨fun ⟨⟨t, ht⟩, h⟩ => ?_, fun ⟨t, h, ht⟩ => ?_⟩
  · exact ⟨⟨t⟩, Value.code_injective h, fun _ hx => ZFSet.mem_powerset.mp ht hx⟩
  · exact ⟨⟨t.codes, ZFSet.mem_powerset.mpr (fun {y} => ht ⟨y⟩)⟩, congrArg Value.code h⟩

end Silmaril.Logic.Temporal.TLA.Data.Tagged
