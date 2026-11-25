module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Evaluation.Thms
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.JumpResolution.Thms
import Silmaril.Proofs.Semantics.Calco2019.Trace.IterationJumpEvaluation

/-! # Denotation preservation for finite jump normalization -/

public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory.Wiring

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (Guardedness.greatest P).Conway)
  {σ : Signature.{w}} {I E : Arity}
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
  {g : Wiring σ I E}

/-- A self-jump denotes bottom. -/
theorem evaluate_cut (s : g.states) (row : g.row s = .jump s) :
    (g.cut s).evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op :=
  Proofs.IterationJumpEvaluation.evaluate_cut F C op g s row

/-- Substituting the destination of a jump preserves evaluation. -/
theorem evaluate_contract (s : g.states) (t : g.without s) (row : g.row s = .jump t.val) :
    (g.contract s t).evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op :=
  Proofs.IterationJumpEvaluation.evaluate_contract F C op g s t row

/-- Every jump resolution preserves evaluation in any total Conway model. -/
theorem Normalizes.evaluate {r : Ranked σ I E} (h : g.Normalizes r) :
    r.toWiring.evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op :=
  Proofs.IterationJumpEvaluation.normalization_evaluate F C op g h

/-- Each input of a ranked graph denotes the solution at its entry state. -/
theorem Ranked.evaluate_component (r : Ranked σ I E) (i : I) :
    (C.cofan I).inj i ≫ r.toWiring.evaluate C F.toFixpoints op =
      (interpretation C F.toFixpoints op).solution F.toFixpoints r.system (r.entry i) :=
  Proofs.IterationJumpEvaluation.ranked_component F C op r i

end Silmaril.Calco2019.IterationTheory.Wiring
