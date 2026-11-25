module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Evaluation.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationWiringEvaluation

/-! # Preservation of denotation by finite equation graph compilation -/

public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (Guardedness.greatest P).Conway)
  {σ : Signature.{w}}
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
  {I J E : Arity}

/-- Connecting exits to the next graph's inputs denotes composition. -/
theorem Wiring.evaluate_comp (f : Wiring σ I J) (g : Wiring σ J E) :
    (f.comp g).evaluate C F.toFixpoints op =
      f.evaluate C F.toFixpoints op ≫ g.evaluate C F.toFixpoints op :=
  Proofs.IterationWiringEvaluation.evaluate_comp F C op f g

/-- Connecting feedback exits to the corresponding entries denotes iteration. -/
theorem Wiring.evaluate_iterate (g : Wiring σ I (E.sum I)) :
    g.iterate.evaluate C F.toFixpoints op =
      F.iterate (g.evaluate C F.toFixpoints op ≫ C.split P E I) True.intro :=
  Proofs.IterationWiringEvaluation.evaluate_iterate F C op g

/-- Compiling a term into a finite equation graph preserves its denotation
in every total Conway interpretation. -/
theorem Term.wiring_evaluate (t : Term σ I E) :
    t.wiring.evaluate C F.toFixpoints op = t.evaluate C F.toFixpoints op :=
  Proofs.IterationWiringEvaluation.term_evaluation F C op t

end Silmaril.Calco2019.IterationTheory
