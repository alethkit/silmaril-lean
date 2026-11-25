module

public import Silmaril.SSA.MLIR.Institution.Syntax.Defs

/-! The quotient of pure syntax by denotation in a selected class of models. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Syntax.Observational

open CategoryTheory

variable {withRegions : Bool} {S : Signature withRegions} (models : Model S → Prop)

/-- The objects are the raw contexts, indexed by the class of models used on arrows. -/
structure Context (models : Model S → Prop) where
  raw : Syntax.Context S

variable {models} {X Y Z W : Context models}

/-- Representatives agree when every selected model gives all result slots the same values
at every typed input. -/
def Rel (models : Model S → Prop) {X Y : Syntax.Context S} (f g : X ⟶ Y) : Prop :=
  ∀ (M : Model S), models M → ∀ (env : Assignment M.carrier X.ty) i,
    (f i).denote M env = (g i).denote M env

def homSetoid (X Y : Context models) : Setoid (X.raw ⟶ Y.raw) where
  r := Rel models
  iseqv :=
    ⟨fun _ _ _ _ _ => rfl, fun h M hM env i => (h M hM env i).symm,
      fun h h' M hM env i => (h M hM env i).trans (h' M hM env i)⟩

theorem comp_rel {f f' : X.raw ⟶ Y.raw} {g g' : Y.raw ⟶ Z.raw}
    (hf : Rel models f f') (hg : Rel models g g') : Rel models (f ≫ g) (f' ≫ g') := by
  intro M hM env i
  change ((g i).subst f).denote M env = ((g' i).subst f').denote M env
  simpa only [Term.denote_subst, funext (hf M hM env)] using hg M hM
    (fun j => (f' j).denote M env) i

instance : Category (Context models) where
  Hom X Y := Quotient (homSetoid X Y)
  id _ := ⟦𝟙 _⟧
  comp f g := Quotient.liftOn₂ f g (fun a b => ⟦a ≫ b⟧)
    (fun _ _ _ _ ha hb => Quotient.sound (comp_rel ha hb))
  id_comp f := Quotient.inductionOn f (fun a => congrArg Quotient.mk'' (Category.id_comp a))
  comp_id f := Quotient.inductionOn f (fun a => congrArg Quotient.mk'' (Category.comp_id a))
  assoc f g h := Quotient.inductionOn₃ f g h
    (fun a b c => congrArg Quotient.mk'' (Category.assoc a b c))

/-- The class of a raw block. -/
def ofBlock (f : X.raw ⟶ Y.raw) : X ⟶ Y := ⟦f⟧

/-- The quotient functor on raw syntax. -/
def quotient (models : Model S → Prop) : Syntax.Context S ⥤ Context models where
  obj X := ⟨X⟩
  map f := ofBlock f
  map_id _ := rfl
  map_comp _ _ := rfl

end Silmaril.MLIR.Institution.Syntax.Observational
