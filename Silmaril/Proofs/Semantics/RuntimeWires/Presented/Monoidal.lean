module

public import Silmaril.Semantics.RuntimeWires.Presented.Defs

public section

namespace Silmaril.RuntimeWires.Proofs

open CategoryTheory Diagram Diagram.Presented

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {E : Equations S}

theorem id_tensorMap_id (A B : Presented S E) :
    tensorMap (𝟙 A) (𝟙 B) = 𝟙 (concat A B) :=
  Quotient.sound (Congruence.tensor_id A.word B.word)

theorem tensorMap_comp {A B C X Y Z : Presented S E}
    (f : A ⟶ B) (g : B ⟶ C) (h : X ⟶ Y) (k : Y ⟶ Z) :
    tensorMap f h ≫ tensorMap g k = tensorMap (f ≫ g) (h ≫ k) :=
  Quotient.inductionOn₃ f g h fun f g h =>
    Quotient.inductionOn k fun k => Quotient.sound (Congruence.tensor_comp f g h k).symm

private theorem tensorMap_eqToHom {A B C D : Presented S E} (h : A = B) (k : C = D) :
    tensorMap (eqToHom h) (eqToHom k) = eqToHom (congrArg₂ concat h k) := by
  subst h
  subst k
  exact id_tensorMap_id A C

private theorem ofTerm_reindex {A B C D : Presented S E} (h : A = C) (k : B = D)
    (f : Diagram S A.word B.word) :
    ofTerm (reindex (congrArg Presented.word h) (congrArg Presented.word k) f) =
      eqToHom h.symm ≫ ofTerm f ≫ eqToHom k := by
  subst h
  subst k
  simp [reindex]

private theorem conj_of_congruence {A B C D : Presented S E} (h : A = C) (k : B = D)
    {f : Diagram S A.word B.word} {g : Diagram S C.word D.word}
    (r : Congruence E (reindex (congrArg Presented.word h) (congrArg Presented.word k) f) g) :
    ofTerm f ≫ eqToHom k = eqToHom h ≫ ofTerm g := by
  have heq : eqToHom h.symm ≫ ofTerm f ≫ eqToHom k = ofTerm g :=
    (ofTerm_reindex h k f).symm.trans (Quotient.sound r)
  simpa using congrArg (fun m => eqToHom h ≫ m) heq

theorem associator_naturality {A B C D X Y : Presented S E}
    (f : A ⟶ B) (g : C ⟶ D) (h : X ⟶ Y) :
    tensorMap (tensorMap f g) h ≫ eqToHom (concat_assoc B D Y) =
      eqToHom (concat_assoc A C X) ≫ tensorMap f (tensorMap g h) :=
  Quotient.inductionOn₃ f g h fun f g h =>
    conj_of_congruence (concat_assoc A C X) (concat_assoc B D Y) (Congruence.tensor_assoc f g h)

theorem leftUnitor_naturality {A B : Presented S E} (f : A ⟶ B) :
    tensorMap (𝟙 empty) f ≫ eqToHom (empty_concat B) = eqToHom (empty_concat A) ≫ f :=
  Quotient.inductionOn f fun f =>
    conj_of_congruence (empty_concat A) (empty_concat B) (Congruence.tensor_unit_left f)

theorem rightUnitor_naturality {A B : Presented S E} (f : A ⟶ B) :
    tensorMap f (𝟙 empty) ≫ eqToHom (concat_empty B) = eqToHom (concat_empty A) ≫ f :=
  Quotient.inductionOn f fun f =>
    conj_of_congruence (concat_empty A) (concat_empty B) (Congruence.tensor_unit_right f)

theorem pentagon (W X Y Z : Presented S E) :
    tensorMap (eqToHom (concat_assoc W X Y)) (𝟙 Z) ≫
        eqToHom (concat_assoc W (concat X Y) Z) ≫
        tensorMap (𝟙 W) (eqToHom (concat_assoc X Y Z)) =
      eqToHom (concat_assoc (concat W X) Y Z) ≫ eqToHom (concat_assoc W X (concat Y Z)) := by
  rw [← eqToHom_refl Z (rfl : Z = Z), ← eqToHom_refl W (rfl : W = W)]
  simp only [tensorMap_eqToHom, eqToHom_trans]

theorem triangle (X Y : Presented S E) :
    eqToHom (concat_assoc X empty Y) ≫ tensorMap (𝟙 X) (eqToHom (empty_concat Y)) =
      tensorMap (eqToHom (concat_empty X)) (𝟙 Y) := by
  rw [← eqToHom_refl X (rfl : X = X), ← eqToHom_refl Y (rfl : Y = Y)]
  simp only [tensorMap_eqToHom, eqToHom_trans]

end Silmaril.RuntimeWires.Proofs
