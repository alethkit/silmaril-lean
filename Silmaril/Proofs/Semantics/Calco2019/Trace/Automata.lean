module

public import Silmaril.Semantics.Calco2019.Trace.Automata.Defs

public section

universe u v u' v' w w'

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {C : Type u'} [Category.{v'} C] {K : Type u} [Category.{v} K]
  {P : Coproducts K} {G : Guardedness P} {X : C} {I : Type w} {L : Type w'} {J : C ⥤ K}
  {c : Cofan (fun _ : I => X)} {a : Cofan (fun _ : L => X)}
  (hc : IsColimit c) (hk : IsColimit (imageCofan J c)) (ha : IsColimit a)

theorem automatonIdentity (F : G.Fixpoints) (uniform : F.Uniform J)
    {Y : K} (step : I → L → I) (body : J.obj X ⟶ P.sum Y (J.obj a.pt))
    (single : G.guarded (body ≫ P.map (𝟙 Y) (J.map (foldStates ha))))
    (multi : G.guarded (automatonBody J hk ha step body)) :
    F.iterate (automatonBody J hk ha step body) multi =
      J.map (foldStates hc) ≫ F.iterate (body ≫ P.map (𝟙 Y) (J.map (foldStates ha))) single := by
  symm
  apply uniform
  have fold_eq (i : I) : c.inj i ≫ foldStates hc = 𝟙 X :=
    Cofan.IsColimit.fac hc _ i
  have select_fold (i : I) : selectStates ha step i ≫ foldStates hc = foldStates ha := by
    apply Cofan.IsColimit.hom_ext ha
    intro l
    have e : a.inj l ≫ selectStates ha step i = c.inj (step i l) := Cofan.IsColimit.fac ha _ l
    rw [← Category.assoc, e, fold_eq]
    exact (Cofan.IsColimit.fac ha (fun _ => 𝟙 X) l).symm
  apply Cofan.IsColimit.hom_ext hk
  intro i
  have inj_fold : (imageCofan J c).inj i ≫ J.map (foldStates hc) = 𝟙 (J.obj X) := by
    change J.map (c.inj i) ≫ J.map (foldStates hc) = 𝟙 (J.obj X)
    rw [← J.map_comp, fold_eq, J.map_id]
  have inj_body := Cofan.IsColimit.fac hk
    (fun i => body ≫ P.map (𝟙 Y) (J.map (selectStates (c := c) ha step i))) i
  change (imageCofan J c).inj i ≫ _ ≫ _ =
    (imageCofan J c).inj i ≫ automatonBody J hk ha step body ≫ _
  change J.map (c.inj i) ≫ J.map (foldStates hc) ≫ _ =
    J.map (c.inj i) ≫ automatonBody J hk ha step body ≫ _
  have inj_fold' : J.map (c.inj i) ≫ J.map (foldStates hc) = 𝟙 (J.obj X) := inj_fold
  have inj_body' : J.map (c.inj i) ≫ automatonBody J hk ha step body =
      body ≫ P.map (𝟙 Y) (J.map (selectStates (c := c) ha step i)) := inj_body
  rw [← Category.assoc, inj_fold', Category.id_comp, ← Category.assoc, inj_body', Category.assoc]
  apply congrArg (body ≫ ·)
  apply P.hom_ext
  · simp [Coproducts.map]
  · simp only [Coproducts.map, P.inr_desc, P.desc_comp]
    rw [Category.assoc, P.inr_desc, ← Category.assoc, ← J.map_comp, select_fold]

end Silmaril.Calco2019.Proofs.Feedback
