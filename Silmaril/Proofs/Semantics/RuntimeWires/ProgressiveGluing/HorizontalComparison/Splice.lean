module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.OrderedKnots.Thms
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.HorizontalComparison

open ProgressiveGraph.OrderedKnots

def knots (a b c d : ℝ) : Fin 4 → ℝ := ![a, b, c, d]

theorem knots_strict {a b c d : ℝ} (ab : a < b) (bc : b < c) (cd : c < d) :
    StrictMono (knots a b c d) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact ab
  · exact bc
  · exact cd

def clamp (a b x : ℝ) : ℝ := max a (min b x)

/-- Insert the given middle map between the two affine continuations.
The correction vanishes on the tails when the middle endpoints match. -/
def splice (a b : Fin 4 → ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  transfer a b x + (f (clamp (a 1) (a 2) x) - transfer a b (clamp (a 1) (a 2) x))

variable {a b : Fin 4 → ℝ} {f g : ℝ → ℝ} {x : ℝ}

theorem splice_middle (h : x ∈ Set.Icc (a 1) (a 2)) : splice a b f x = f x := by
  rw [splice, clamp, min_eq_right h.2, max_eq_right h.1]
  ring

theorem splice_low (ha : StrictMono a) (hf : f (a 1) = b 1) (h : x ≤ a 1) :
    splice a b f x = transfer a b x := by
  rw [splice, clamp, max_eq_left ((min_le_right _ _).trans h), hf, transfer_knot ha, sub_self, add_zero]

theorem splice_high (ha : StrictMono a) (hf : f (a 2) = b 2) (h : a 2 ≤ x) :
    splice a b f x = transfer a b x := by
  have e : a 1 ≤ a 2 := (ha (by decide : (1 : Fin 4) < 2)).le
  rw [splice, clamp, min_eq_left h, max_eq_right e, hf, transfer_knot ha, sub_self, add_zero]

theorem splice_self (ha : StrictMono a) (x : ℝ) : splice a a id x = x := by
  simp only [splice, transfer_self ha, id_eq, sub_self, add_zero]

theorem splice_inverse (ha : StrictMono a) (hb : StrictMono b) (hf : StrictMono f)
    (lo : f (a 1) = b 1) (hi : f (a 2) = b 2) (inv : Function.LeftInverse g f) (x : ℝ) :
    splice b a g (splice a b f x) = x := by
  have glo : g (b 1) = a 1 := lo ▸ inv (a 1)
  have ghi : g (b 2) = a 2 := hi ▸ inv (a 2)
  by_cases hl : x ≤ a 1
  · have ht : transfer a b x ≤ b 1 :=
      (transfer_knot (b := b) ha 1) ▸ (transfer_strictMono ha hb).monotone hl
    rw [splice_low ha lo hl, splice_low hb glo ht, transfer_inverse ha hb]
  · by_cases hh : a 2 ≤ x
    · have ht : b 2 ≤ transfer a b x :=
        (transfer_knot (b := b) ha 2) ▸ (transfer_strictMono ha hb).monotone hh
      rw [splice_high ha hi hh, splice_high hb ghi ht, transfer_inverse ha hb]
    · have h : x ∈ Set.Icc (a 1) (a 2) := ⟨le_of_not_ge hl, le_of_not_ge hh⟩
      have hx : f x ∈ Set.Icc (b 1) (b 2) :=
        ⟨lo ▸ hf.monotone h.1, hi ▸ hf.monotone h.2⟩
      rw [splice_middle h, splice_middle hx, inv]

theorem splice_continuous {a b : ℝ → Fin 4 → ℝ} (ha : ∀ y, StrictMono (a y))
    (ca : ∀ i, Continuous fun y => a y i) (cb : ∀ i, Continuous fun y => b y i)
    {f : ℝ × ℝ → ℝ} (cf : Continuous f) :
    Continuous fun z : ℝ × ℝ => splice (a z.2) (b z.2) (fun x => f (x, z.2)) z.1 := by
  have cl : Continuous fun z : ℝ × ℝ => clamp (a z.2 1) (a z.2 2) z.1 :=
    ((ca 1).comp continuous_snd).max (((ca 2).comp continuous_snd).min continuous_fst)
  have tr {g : ℝ × ℝ → ℝ} (cg : Continuous g) :
      Continuous fun z : ℝ × ℝ => transfer (a z.2) (b z.2) (g z) :=
    continuous_transfer (fun i => (ca i).comp continuous_snd) (fun i => (cb i).comp continuous_snd)
      (fun z => ha z.2) cg
  exact (tr continuous_fst).add ((cf.comp (cl.prodMk continuous_snd)).sub (tr cl))

end Silmaril.RuntimeWires.Proofs.HorizontalComparison
