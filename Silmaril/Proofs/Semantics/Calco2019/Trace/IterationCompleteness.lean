module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Completeness.Defs

public section

universe u v w

namespace Silmaril.Calco2019.Proofs.IterationCompleteness

open CategoryTheory CategoryTheory.Limits Guardedness IterationTheory
open OmegaCompletePartialOrder Silmaril.Semantics.Domain

private theorem pointed_bottom {X Y : PointedModel.Object.{u}} :
    PointedModel.conway.iterate
      (PointedModel.coproducts.inr (X := Y) (Y := X)) True.intro = ⊥ := by
  apply ContinuousHom.ext
  intro y
  rw [PointedModel.least_at]
  have body :
      (PointedModel.run (PointedModel.coproducts.inr (X := Y) (Y := X))).comp
        (pairHom (ContinuousHom.const y) ContinuousHom.id) = ContinuousHom.id := by
    apply ContinuousHom.ext
    intro x
    rfl
  rw [body]
  exact le_antisymm (fix_le (f := ContinuousHom.id) le_rfl) bot_le

private theorem path_interpretation (σ : Signature.{u}) (E : Arity) :
    Wiring.interpretation
        (PointedModel.copowers (PointedModel.of (PathDomain σ E)))
        PointedModel.conway.toFixpoints (PointedModel.pathOperation (σ := σ) (E := E)) =
      PointedModel.pathInterpretation σ E := by
  unfold Wiring.interpretation PointedModel.pathInterpretation
  congr 1
  exact pointed_bottom

theorem path_complete {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
    (C : FiniteCopowers X) (F : (greatest P).Conway) (comm : C.CommutativeIdentities F.toFixpoints)
    {σ : Signature.{w}} {I E : Arity} (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
    (f g : Term σ I E) (same : f.pathDenotation = g.pathDenotation) :
    f.evaluate C F.toFixpoints op = g.evaluate C F.toFixpoints op := by
  obtain ⟨r, rf⟩ := f.wiring.exists_normalization
  obtain ⟨s, sg⟩ := g.wiring.exists_normalization
  let D := PointedModel.of (PathDomain σ E)
  let Dcop := PointedModel.copowers D
  let DF := PointedModel.conway.{w}
  let Dop := PointedModel.pathOperation (σ := σ) (E := E)
  have same_terms : f.evaluate Dcop DF.toFixpoints Dop = g.evaluate Dcop DF.toFixpoints Dop := same
  have same_graphs : r.toWiring.evaluate Dcop DF.toFixpoints Dop =
      s.toWiring.evaluate Dcop DF.toFixpoints Dop :=
    (rf.evaluate Dcop DF Dop).trans ((f.wiring_evaluate Dcop DF Dop).trans
      (same_terms.trans ((g.wiring_evaluate Dcop DF Dop).symm.trans (sg.evaluate Dcop DF Dop).symm)))
  have component (i : I) :
      (PointedModel.pathInterpretation σ E).solution DF.toFixpoints r.system (r.entry i) =
      (PointedModel.pathInterpretation σ E).solution DF.toFixpoints s.system (s.entry i) := by
    rw [← path_interpretation]
    exact (r.evaluate_component Dcop DF Dop i).symm.trans
      ((congrArg (fun k => (Dcop.cofan I).inj i ≫ k) same_graphs).trans (s.evaluate_component Dcop DF Dop i))
  have same_ranked : r.toWiring.evaluate C F.toFixpoints op = s.toWiring.evaluate C F.toFixpoints op := by
    apply Cofan.IsColimit.hom_ext (C.colimit I)
    intro i
    rw [r.evaluate_component C F op i, s.evaluate_component C F op i]
    exact (Wiring.interpretation C F.toFixpoints op).solution_of_standard_commutative F comm
      r.system s.system (r.entry i) (s.entry i)
      ((PointedModel.path_solution_eq_iff r.system s.system (r.entry i) (s.entry i)).mp (component i))
  exact (f.wiring_evaluate C F op).symm.trans ((rf.evaluate C F op).symm.trans
    (same_ranked.trans ((sg.evaluate C F op).trans (g.wiring_evaluate C F op))))

theorem pointed_iff_path {σ : Signature.{u}} {I E : Arity} (f g : Term σ I E) :
    f.ValidInPointedDomains g ↔ f.pathDenotation = g.pathDenotation := by
  constructor
  · intro valid
    exact valid (PointedModel.of (PathDomain σ E)) (PointedModel.pathOperation (σ := σ) (E := E))
  · intro same D op
    exact path_complete (PointedModel.copowers D) PointedModel.conway (PointedModel.commutative D) op f g same

end Silmaril.Calco2019.Proofs.IterationCompleteness
