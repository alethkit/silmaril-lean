module

public import Silmaril.SSA.MLIR.Institution.Syntax.Observational.Defs
public import Silmaril.SSA.MLIR.Institution.Translation.Thms

@[expose] public section

namespace Silmaril.MLIR.Institution.Syntax.Observational

open CategoryTheory

variable {withRegions : Bool} {S T : Signature withRegions}
variable {models : Model S → Prop} {targetModels : Model T → Prop}
variable {X Y : Context models}

/-- Equality of block classes is exactly agreement in the selected models. -/
theorem ofBlock_eq_iff {f g : X.raw ⟶ Y.raw} :
    ofBlock (X := X) (Y := Y) f = ofBlock g ↔ Rel models f g :=
  ⟨Quotient.exact, Quotient.sound (s := homSetoid X Y)⟩

/-- Every selected model interprets quotient arrows as total functions. -/
def denote (M : Model S) (hM : models M) : Context models ⥤ Type where
  obj X := (Syntax.denote M).obj X.raw
  map f := Quotient.liftOn f (Syntax.denote M).map
    (fun _ _ h => congrArg TypeCat.ofHom (funext fun env => funext (h M hM env)))
  map_id _ := rfl
  map_comp f g := Quotient.inductionOn₂ f g (Syntax.denote M).map_comp

theorem quotient_denote (M : Model S) (hM : models M) :
    quotient models ⋙ denote M hM = Syntax.denote M :=
  Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

/-- An interpretation descends if reducts of the selected target models are selected at
the source. -/
def translate (f : Interpretation S T) (compatible : ∀ M, targetModels M → models (f.reduct M)) :
    Context models ⥤ Context targetModels where
  obj X := ⟨f.syntaxFunctor.obj X.raw⟩
  map σ := Quotient.liftOn σ (fun a => ofBlock (f.syntaxFunctor.map a))
    (fun _ _ h => Quotient.sound fun M hM env i =>
      (f.denote_term M _ env).trans
        ((h (f.reduct M) (compatible M hM) env i).trans (f.denote_term M _ env).symm))
  map_id _ := rfl
  map_comp σ τ := Quotient.inductionOn₂ σ τ (fun a b => congrArg ofBlock (f.syntaxFunctor.map_comp a b))

theorem quotient_translate (f : Interpretation S T)
    (compatible : ∀ M, targetModels M → models (f.reduct M)) :
    quotient models ⋙ translate f compatible = f.syntaxFunctor ⋙ quotient targetModels :=
  Functor.ext (fun _ => rfl) (fun _ _ σ => by
    change _ = 𝟙 _ ≫ ofBlock (f.syntaxFunctor.map σ) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    rfl)

end Silmaril.MLIR.Institution.Syntax.Observational
