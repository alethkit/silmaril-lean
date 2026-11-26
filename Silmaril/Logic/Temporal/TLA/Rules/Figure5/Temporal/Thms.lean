module

public import Silmaril.Logic.Temporal.TLA.Rules.Figure5.Temporal.Defs
public import Silmaril.Logic.Temporal.TLA.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Rules.Figure5.Temporal.Soundness

/-! The simple temporal logic and Lattice rules of Lamport Fig. 5. -/

public section

namespace Silmaril.Logic.Temporal.TLA.Rules.Figure5

open Formula

universe u v

variable {S : Type u} {ι : Type v}

/-- Propositional deduction is sound at any instant satisfying its context. -/
theorem PropDerives.sound {Γ : List (Formula S)} {F : Formula S} (proof : PropDerives Γ F)
    (σ : Behavior S) (i : Nat) (valid : ∀ G ∈ Γ, G.Holds σ i) : F.Holds σ i :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.propDerives_sound proof σ i valid

/-- STL1. The context may be empty for a propositional tautology, or contain
previously proved formulas whose validity is supplied as a premise (Note 11). -/
theorem stl1 {Γ : List (Formula S)} {F : Formula S} (proof : PropDerives Γ F)
    (valid : ∀ G ∈ Γ, ∀ σ, G.Sat σ) (σ : Behavior S) : (always F).Sat σ :=
  fun i _ => proof.sound σ i fun G hG => (G.sat_suffix σ i).mp (valid G hG (σ.suffix i))

/-- STL2. The current instant is included in `□F`. -/
theorem stl2 (F : Formula S) : (always F).Entails F :=
  fun _ h => h 0 (Nat.le_refl 0)

/-- STL3. `□□F` is equivalent to `□F`. -/
theorem stl3 (F : Formula S) (σ : Behavior S) : (always (always F)).Sat σ ↔ (always F).Sat σ :=
  ⟨fun h => h 0 (Nat.le_refl 0), fun h _ hi j hj => h j (Nat.le_trans hi hj)⟩

/-- STL4. A valid implication remains valid under `□` on both sides. -/
theorem stl4 {F G : Formula S} (implies : F.Entails G) : (always F).Entails (always G) :=
  fun σ hF i hi => (G.sat_suffix σ i).mp (implies (σ.suffix i) ((F.sat_suffix σ i).mpr (hF i hi)))

/-- STL5. `□` distributes over conjunction. -/
theorem stl5 (F G : Formula S) (σ : Behavior S) :
    (always (conj F G)).Sat σ ↔ (conj (always F) (always G)).Sat σ :=
  ⟨fun h => ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩,
    fun h i hi => ⟨h.1 i hi, h.2 i hi⟩⟩

/-- STL6. Two eventual permanent properties share a permanent tail. -/
theorem stl6 (F G : Formula S) (σ : Behavior S) :
    (conj (eventually (always F)) (eventually (always G))).Sat σ ↔
      (eventually (always (conj F G))).Sat σ :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.stl6 F G σ

/-- Lattice. `smaller d c` means `c ≻ d` in Fig. 5. Membership in the index set
is represented by `c : ι`, and the leads-to expressions are expanded at their
satisfaction instants to express the existential over the rigid index family.
The premise and conclusion both test `F` at the initial instant. -/
theorem lattice {smaller : ι → ι → Prop} (order : WellFounded smaller)
    {F G : Formula S} {H : ι → Formula S}
    (step : ∀ c σ, F.Sat σ → ∀ i, (H c).Holds σ i →
      ∃ j, i ≤ j ∧ (G.Holds σ j ∨ ∃ d, smaller d c ∧ (H d).Holds σ j)) :
    ∀ σ, F.Sat σ → ∀ i, (∃ c, (H c).Holds σ i) → ∃ j, i ≤ j ∧ G.Holds σ j :=
  Proofs.Logic.Temporal.TLA.Rules.Figure5.lattice order step

end Silmaril.Logic.Temporal.TLA.Rules.Figure5
