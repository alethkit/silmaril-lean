module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay

universe w x

variable {n m : Nat} {α : Type w} {σ : Type x}

private theorem possible_mono {p q : Behaviour n α σ} (h : p ≤ q) :
    p.possible ⊆ q.possible := by
  cases q using WithTop.recTopCoe
  · exact Set.subset_univ _
  cases p using WithTop.recTopCoe
  · exact (WithTop.not_top_le_coe _ h).elim
  · exact WithTop.coe_le_coe.mp h

theorem bind_mono {p q : Behaviour n α σ}
    {k h : Fin n → Value α → σ → Behaviour m α σ}
    (pq : p ≤ q) (kh : ∀ i a s, k i a s ≤ h i a s) : p.bind k ≤ q.bind h := by
  classical
  unfold Behaviour.bind
  split_ifs with pt qt qt
  · exact le_rfl
  · exfalso
    apply qt
    rcases pt with rfl | ⟨i, a, s, reached, atTop⟩
    · exact Or.inl (top_le_iff.mp pq)
    · exact Or.inr ⟨i, a, s, possible_mono pq reached,
        top_le_iff.mp (atTop ▸ kh i a s)⟩
  · exact le_top
  · apply WithTop.coe_le_coe.mpr
    intro o ho
    rcases ho with hx | ⟨i, a, s, hx, hk⟩
    · apply Or.inl
      cases o with
      | ret _ _ _ => exact hx
      | fault _ | diverge => exact possible_mono pq hx
    · exact Or.inr ⟨i, a, s, possible_mono pq hx, possible_mono (kh i a s) hk⟩

theorem coe_bind (p : Set (Outcome n α σ)) (k : Fin n → Value α → σ → Set (Outcome m α σ)) :
    Behaviour.bind (m := m) (↑p : Behaviour n α σ) (fun i a s => ↑(k i a s)) = ↑(Outcome.bind p k) := by
  classical
  simp [Behaviour.bind, Behaviour.possible]

/-- The empty source interface has no successful exit to continue from. -/
theorem bind_empty_ne_univ {i : Fin m} (a : Value α) (s : σ)
    (k : Fin 0 → Value α → σ → Set (Outcome m α σ)) :
    Outcome.bind Set.univ k ≠ Set.univ := by
  intro eq
  have ret : Outcome.ret i a s ∈ Outcome.bind Set.univ k := eq.symm ▸ Set.mem_univ _
  rcases ret with ho | ⟨j, _, _, _, _⟩
  · exact ho
  · exact Fin.elim0 j

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
