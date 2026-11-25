module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Interpretation.Defs

public section

universe u v w z

namespace Silmaril.Calco2019.Proofs.IterationInterpretation

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory
open Silmaril.Semantics.Domain

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
  {C : FiniteCopowers X} {σ : Signature.{w}} {E : Type z}
  (M : Interpretation C σ E Y) {S T : Type} [Finite S] [Finite T]

@[reassoc (attr := simp)] theorem reindex_inj (f : S → T) (s : S) :
    (C.cofan S).inj s ≫ C.reindex f = (C.cofan T).inj (f s) :=
  Cofan.IsColimit.fac (C.colimit S) _ s

theorem reindex_comp {R : Type} [Finite R] (f : R → S) (g : S → T) :
    C.reindex f ≫ C.reindex g = C.reindex (g ∘ f) := by
  apply Cofan.IsColimit.hom_ext (C.colimit R)
  intro r
  simp

theorem branch_reindex (f : S → T) (e : Head σ E S) :
    M.branch (P := P) e ≫ P.map (𝟙 Y) (C.reindex f) =
      M.branch (P := P) (e.mapState f) := by
  cases e <;> simp [Interpretation.branch, Head.mapState, Coproducts.map]
  rename_i sym child
  rw [← Category.assoc (C.reindex child) (C.reindex f), reindex_comp]

theorem body_square {g : System σ E S} {h : System σ E T} {f : S → T}
    (respects : PreservesEquations g h f) :
    C.reindex f ≫ M.body (P := P) h =
      M.body (P := P) g ≫ P.map (𝟙 Y) (C.reindex f) := by
  apply Cofan.IsColimit.hom_ext (C.colimit S)
  intro s
  rw [reindex_inj_assoc]
  have g_branch : (C.cofan S).inj s ≫ M.body (P := P) g = M.branch (g s) :=
    Cofan.IsColimit.fac (C.colimit S) _ s
  have h_branch : (C.cofan T).inj (f s) ≫ M.body (P := P) h = M.branch (h (f s)) :=
    Cofan.IsColimit.fac (C.colimit T) _ (f s)
  rw [h_branch, ← Category.assoc, g_branch, branch_reindex, respects s]

theorem solution_of_map (F : (Guardedness.greatest P).Fixpoints)
    {g : System σ E S} {h : System σ E T} {f : S → T}
    (uniform : F.UniformAt (C.reindex f)) (respects : PreservesEquations g h f) (s : S) :
    M.solution F g s = M.solution F h (f s) := by
  have e := uniform (M.body h) (M.body g) True.intro True.intro (body_square M respects)
  unfold Interpretation.solution
  rw [← e, reindex_inj_assoc]

theorem solution_of_standard_equality (F : (Guardedness.greatest P).Fixpoints) (uniform : C.BaseUniform F)
    (g : System σ E S) (h : System σ E T) (s : S) (t : T)
    (same : fix (update g) s = fix (update h) t) :
    M.solution F g s = M.solution F h t := by
  obtain ⟨R, finite, k, left, right, root, hl, hr, rfl, rfl⟩ :=
    (least_eq_iff_finite_span g h s t).1 same
  exact (solution_of_map M F (uniform left) hl root).symm.trans
    (solution_of_map M F (uniform right) hr root)

end Silmaril.Calco2019.Proofs.IterationInterpretation
