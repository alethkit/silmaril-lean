module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Expansion.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationExpansion

/-! # Realize each expanded equation by reindexing its representative -/

public section

universe u v w z

namespace Silmaril.Calco2019.IterationTheory

variable {σ : Signature.{u}} {E : Type v} {S : Type w} {T : Type z}
  (g : System σ E S) (pick : T → S) (p : S → T)

instance expandedState_finite [Finite S] [Finite T] : Finite (ExpandedState g pick) :=
  Proofs.IterationExpansion.expansion_finite g pick

theorem expanded_inclusion : PreservesEquations g (expandedSystem g pick) Sum.inl :=
  fun _ => rfl

theorem expandedProjection_surjective (section_eq : ∀ t, p (pick t) = t) :
    Function.Surjective (expandedProjection g pick p) :=
  fun t => ⟨.inl (pick t), section_eq t⟩

theorem representative_respects {h : System σ E T} (map : PreservesEquations g h p)
    (section_eq : ∀ t, p (pick t) = t) (t : T) :
    (representativeBody g pick t).mapState (expandedProjection g pick p) = h t :=
  Proofs.IterationExpansion.representative_respects g pick p map section_eq t

/-- Expanded equations are obtained from the representative equations by
routes that preserve fibers of the projection. -/
theorem expansion_routes {h : System σ E T} (map : PreservesEquations g h p)
    (section_eq : ∀ t, p (pick t) = t) :
    ∃ route : ExpandedState g pick → ExpandedState g pick → ExpandedState g pick,
      (∀ x y, expandedProjection g pick p (route x y) = expandedProjection g pick p y) ∧
      (∀ x, (representativeBody g pick (expandedProjection g pick p x)).mapState (route x) =
        expandedSystem g pick x) :=
  Proofs.IterationExpansion.expansion_routes g pick p map section_eq

end Silmaril.Calco2019.IterationTheory
