module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Interpretation.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationInterpretation

/-! # Reindexing and solution invariance for ranked systems -/

public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory CategoryTheory.Limits
open Silmaril.Semantics.Domain

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X Y : K}
  {C : FiniteCopowers X} {σ : Signature.{w}} {E : Type z}
  (M : Interpretation C σ E Y) {S T : Type} [Finite S] [Finite T]

@[reassoc (attr := simp)]
theorem FiniteCopowers.reindex_inj (f : S → T) (s : S) :
    (C.cofan S).inj s ≫ C.reindex f = (C.cofan T).inj (f s) :=
  Proofs.IterationInterpretation.reindex_inj f s

theorem FiniteCopowers.reindex_comp {R : Type} [Finite R] (f : R → S) (g : S → T) :
    C.reindex f ≫ C.reindex g = C.reindex (g ∘ f) :=
  Proofs.IterationInterpretation.reindex_comp f g

theorem Interpretation.body_square {g : System σ E S} {h : System σ E T} {f : S → T}
    (respects : PreservesEquations g h f) :
    C.reindex f ≫ M.body (P := P) h =
      M.body g ≫ P.map (𝟙 Y) (C.reindex f) :=
  Proofs.IterationInterpretation.body_square M respects

/-- Uniformity at the corresponding base map transports solutions for a map
of ranked equation systems. -/
theorem Interpretation.solution_of_map (F : (Guardedness.greatest P).Fixpoints)
    {g : System σ E S} {h : System σ E T} {f : S → T}
    (uniform : F.UniformAt (C.reindex f)) (respects : PreservesEquations g h f) (s : S) :
    M.solution F g s = M.solution F h (f s) :=
  Proofs.IterationInterpretation.solution_of_map M F uniform respects s

/-- Equality in the pointed path domain implies equality in every
interpretation that satisfies finite base-map uniformity. -/
theorem Interpretation.solution_of_standard_equality (F : (Guardedness.greatest P).Fixpoints)
    (uniform : C.BaseUniform F) (g : System σ E S) (h : System σ E T) (s : S) (t : T)
    (same : fix (update g) s = fix (update h) t) :
    M.solution F g s = M.solution F h t :=
  Proofs.IterationInterpretation.solution_of_standard_equality M F uniform g h s t same

end Silmaril.Calco2019.IterationTheory
