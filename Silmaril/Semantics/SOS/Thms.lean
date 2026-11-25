module

public import Silmaril.Semantics.SOS.Defs
public import Mathlib.Order.Monotone.Defs
import Silmaril.Proofs.Semantics.SOS.Closure

@[expose] public section

namespace Silmaril.Semantics.SOS

universe u v w

@[simp] theorem Rule.map_id {J : Type u} (r : Rule J) : r.map id = r := by
  cases r
  simp [Rule.map]

theorem Rule.map_comp {J : Type u} {K : Type v} {L : Type w}
    (f : J → K) (g : K → L) (r : Rule J) : r.map (g ∘ f) = (r.map f).map g := by
  simp [Rule.map, List.map_map]

/-- Clause satisfaction commutes with predicate pullback, including for noninjective maps. -/
theorem Rule.holds_map {J : Type u} {K : Type v} (f : J → K) (M : K → Prop) (r : Rule J) :
    (r.map f).Holds M ↔ r.Holds (M ∘ f) := by
  simp only [Rule.Holds, Rule.map, List.forall_mem_map, Function.comp_apply]

theorem immediate_mono {J : Type u} (R : Set (Rule J)) :
    Monotone (immediate R) :=
  fun _ _ h _ ⟨r, hr, eq, premises⟩ => ⟨r, hr, eq, fun j hj => h j (premises j hj)⟩

theorem derives_closed {J : Type u} (R : Set (Rule J)) : Closed R (Derives R) :=
  fun _ hr premises => .apply hr premises

/-- Every closed predicate contains all derivable judgments. -/
theorem Derives.least {J : Type u} {R : Set (Rule J)} {M : J → Prop} {j : J}
    (h : Derives R j) (closed : Closed R M) : M j := by
  induction h with
  | apply hr _ ih => exact closed _ hr ih

/-- Derivability is a fixed point of the immediate consequence operator. -/
theorem immediate_derives {J : Type u} (R : Set (Rule J)) :
    immediate R (Derives R) = Derives R :=
  funext fun _ => propext Proofs.immediate_iff

/-- Derivability is contained in every pre-fixed point of immediate consequence. -/
theorem derives_le_of_immediate_le {J : Type u} {R : Set (Rule J)} {M : J → Prop}
    (h : immediate R M ≤ M) : Derives R ≤ M :=
  fun _ hj => hj.least fun r hr premises => h r.conclusion ⟨r, hr, rfl, premises⟩

/-- A renaming that sends every source rule to a target rule preserves derivability. -/
theorem Derives.map {J : Type u} {K : Type v} {R : Set (Rule J)} {Q : Set (Rule K)}
    (f : J → K) (preserves : ∀ r ∈ R, r.map f ∈ Q) {j : J} (h : Derives R j) :
    Derives Q (f j) :=
  h.least fun r hr => (r.holds_map f (Derives Q)).mp (derives_closed Q _ (preserves r hr))

end Silmaril.Semantics.SOS
