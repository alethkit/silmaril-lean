module

public import Silmaril.Semantics.Calco2019.Trace.Equivalence.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}

private theorem onBranches_ofConway (F : G.Conway) {A B U : K}
    (entry : A ⟶ P.sum B U) (body : U ⟶ P.sum B U) (hb : G.guarded body) :
    Feedback.onBranches F.toFixpoints.feedback entry body hb =
      entry ≫ P.desc (𝟙 B) (F.iterate body hb) := by
  change P.inl ≫ P.desc entry body ≫ P.desc (𝟙 B) (F.iterate (P.inr ≫ P.desc entry body) _) = _
  rw [P.inl_desc_assoc]
  exact congrArg (fun s => entry ≫ P.desc (𝟙 B) s)
    (iterate_eq F.toFixpoints (P.inr_desc entry body) _ hb)

theorem pairVanishing_ofConway (F : G.Conway) : Feedback.PairVanishing F.toFixpoints.feedback := by
  intro A B U V D h
  dsimp only
  refine (onBranches_ofConway F _ _ D.guarded).trans ?_
  refine Eq.trans ?_ (onBranches_ofConway F _ _ h).symm
  have compare (s : V ⟶ P.sum B U) (e : s = F.iterate D.second D.second_guard)
      (hs : G.guarded (D.first ≫ P.desc (𝟙 _) s)) :
      D.entry ≫ P.assoc ≫ P.desc (𝟙 B) (F.iterate (P.desc D.first D.second ≫ P.assoc) D.guarded) =
        (D.entry ≫ P.desc (𝟙 _) s) ≫ P.desc (𝟙 B) (F.iterate _ hs) := by
    subst s
    simpa only [Category.assoc] using D.feedback_vanish_pair F
  exact (Category.assoc _ _ _).trans
    (compare _ (Guardedness.feedback_recovers F.toFixpoints D.second D.second_guard) h)

theorem feedback_codiagonal [HasInitial K] {trace : G.Feedback} (laws : Feedback.Lawful trace) :
    (Feedback.fixpoints laws.toLocalLaws).NaturalCodiagonal := by
  constructor
  · intro U B B' f b hf hg
    exact Feedback.iterate_natural laws.toLocalLaws f b hf hg
  · intro X Y f hf hinner houter hmerged
    let D : TwoStateBody G X Y X X := ⟨f, f, f, by
      change G.guarded (P.desc f f ≫ P.assoc)
      rw [P.desc_comp]
      exact G.parallel hf hf⟩
    let g := f ≫ P.assoc
    let q := (P.desc (𝟙 X) (𝟙 X)) ≫ (P.inr : X ⟶ P.sum Y X)
    let b := P.desc g g
    have guard : G.guarded (P.inr ≫ b) ∨ G.guarded q :=
      Or.inl (by simpa [b, g] using (show G.guarded (f ≫ P.assoc) from hf))
    have fold_eq : P.assoc ≫ P.desc P.inl q = (P.merge : P.sum (P.sum Y X) X ⟶ P.sum Y X) := by
      simp [Coproducts.assoc, Coproducts.merge, q]
    have first : slideAfter b q = P.desc (f ≫ P.merge) (f ≫ P.merge) := by
      simp [slideAfter, b, g, fold_eq]
    have second : slideBefore b q = P.desc g (P.desc f f ≫ P.assoc) := by
      simp [slideBefore, b, g, q]
    let h := Feedback.iterate trace f hinner
    have finish_entry : f ≫ P.desc (𝟙 _) h = h :=
      (Feedback.fixpoints laws.toLocalLaws).fixpoint f hinner
    have hstage : G.guarded (D.first ≫ P.desc (𝟙 _) (Feedback.iterate trace D.second D.second_guard)) :=
      finish_entry.symm ▸ houter
    have vanish := laws.vanishPair D hstage
    change Feedback.onBranches trace g (P.desc f f ≫ P.assoc) D.guarded =
      Feedback.onBranches trace (f ≫ P.desc (𝟙 _) h) (f ≫ P.desc (𝟙 _) h) hstage at vanish
    change Feedback.iterate trace (f ≫ P.merge) hmerged = Feedback.iterate trace h houter
    exact (trace_eq first.symm _ (slideAfter_guard b q guard)).trans
      ((laws.slide b q guard).trans ((trace_eq second _ _).trans
        (vanish.trans (trace_eq (congrArg₂ P.desc finish_entry finish_entry) _ _))))

end Silmaril.Calco2019.Proofs.Feedback
