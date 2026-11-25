module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Encoding
public import Silmaril.Proofs.Semantics.RuntimeWires.Sliced.Soundness
public import Silmaril.Proofs.Semantics.RuntimeWires.Coherence.Transport

public section

namespace Silmaril.RuntimeWires.Proofs.SlicedCompleteness

open CategoryTheory Silmaril.RuntimeWires.Sliced
open scoped MonoidalCategory SameArrow

universe u v

variable {O : Type u} {S : Signature.{u,v} O} (E : Diagram.Equations S)

local notation "Obj" => (Diagram.Presented.mk (S := S) (E := E))

private theorem row_reindex_denote {A B X Y : List O} (p : A = X) (q : B = Y) (r : Row S A B) :
    (r.reindex p q).denote E ≈ₐ r.denote E := by
  subst p
  subst q
  exact SameArrow.refl _

private theorem sheet_reindex_denote {A B X Y : List O} (p : A = X) (q : B = Y) (r : Sheet S A B) :
    (r.reindex p q).denote E ≈ₐ r.denote E := by
  subst p
  subst q
  exact SameArrow.refl _

private theorem assoc {A B X Y U V : Diagram.Presented S E}
    (f : A ⟶ B) (g : X ⟶ Y) (h : U ⟶ V) :
    (f ⊗ₘ g) ⊗ₘ h ≈ₐ f ⊗ₘ (g ⊗ₘ h) := by
  have src := Diagram.Presented.concat_assoc A X U
  have dst := Diagram.Presented.concat_assoc B Y V
  have square : ((f ⊗ₘ g) ⊗ₘ h) ≫ eqToHom dst =
      eqToHom src ≫ (f ⊗ₘ (g ⊗ₘ h)) := MonoidalCategory.associator_naturality f g h
  have eq : ((f ⊗ₘ g) ⊗ₘ h) = eqToHom src ≫ (f ⊗ₘ (g ⊗ₘ h)) ≫ eqToHom dst.symm := by
    have h := congrArg (· ≫ eqToHom dst.symm) square
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h
  exact ⟨src, dst, (conj_eqToHom_iff_heq _ _ src dst).mp eq⟩

private theorem denote_beside {A B X Y : List O} (r : Row S A B) (s : Row S X Y) :
    (r.beside s).denote E = r.denote E ⊗ₘ s.denote E := by
  induction r with
  | empty => exact Silmaril.RuntimeWires.Proofs.Sliced.denote_pass E [] s
  | wire x r ih =>
    change (𝟙 (Obj [x])) ⊗ₘ (r.beside s).denote E =
      ((𝟙 (Obj [x])) ⊗ₘ r.denote E) ⊗ₘ s.denote E
    exact (((SameArrow.refl (𝟙 (Obj [x]))).tensor (.of_eq ih)).trans
      (assoc E (𝟙 (Obj [x])) (r.denote E) (s.denote E)).symm).eq
  | box e r ih =>
    let f : Obj (S.source e) ⟶ Obj (S.target e) := Diagram.Presented.ofTerm (.gen e)
    exact ((row_reindex_denote E _ _ (.box e (r.beside s))).trans
      (((SameArrow.refl f).tensor (.of_eq ih)).trans (assoc E f (r.denote E) (s.denote E)).symm)).eq

theorem denote_then {A B C : List O} (p : Sheet S A B) (q : Sheet S B C) :
    (p.thenDo q).denote E = p.denote E ≫ q.denote E := by
  induction p with
  | empty => exact (Category.id_comp _).symm
  | cons r p ih =>
    change r.denote E ≫ (p.thenDo q).denote E = (r.denote E ≫ p.denote E) ≫ q.denote E
    rw [ih, Category.assoc]

private theorem denote_padLeft (W : List O) {A B : List O} (p : Sheet S A B) :
    (p.padLeft W).denote E = (𝟙 (Obj W)) ⊗ₘ p.denote E := by
  induction p with
  | empty A => exact (MonoidalCategory.id_tensorHom_id _ _).symm
  | cons r p ih =>
    simp only [Sheet.padLeft, Sheet.denote, Silmaril.RuntimeWires.Proofs.Sliced.denote_pass E W, ih]
    exact (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 (Obj W)) (r.denote E)
      (𝟙 (Obj W)) (p.denote E)).trans (congrArg (· ⊗ₘ (r.denote E ≫ p.denote E)) (Category.id_comp _))

private theorem denote_padRight (W : List O) {A B : List O} (p : Sheet S A B) :
    (p.padRight W).denote E = p.denote E ⊗ₘ (𝟙 (Obj W)) := by
  induction p with
  | empty A => exact (MonoidalCategory.id_tensorHom_id _ _).symm
  | cons r p ih =>
    simp only [Sheet.padRight, Sheet.denote, denote_beside E, Silmaril.RuntimeWires.Proofs.Sliced.denote_straight E W, ih]
    exact (MonoidalCategory.tensorHom_comp_tensorHom (r.denote E) (𝟙 (Obj W))
      (p.denote E) (𝟙 (Obj W))).trans (congrArg ((r.denote E ≫ p.denote E) ⊗ₘ ·) (Category.id_comp _))

theorem denote_tensor {A B X Y : List O} (p : Sheet S A B) (q : Sheet S X Y) :
    (p.tensor q).denote E = p.denote E ⊗ₘ q.denote E := by
  simp only [Sheet.tensor, denote_then E, denote_padRight E, denote_padLeft E]
  exact (MonoidalCategory.tensorHom_comp_tensorHom (p.denote E) (𝟙 (Obj X))
    (𝟙 (Obj B)) (q.denote E)).trans
      (congrArg₂ (· ⊗ₘ ·) (Category.comp_id _) (Category.id_comp _))

private theorem term_reindex {A B X Y : List O} (p : A = X) (q : B = Y) (f : Diagram S A B) :
    Diagram.Presented.ofTerm (A := Obj X) (B := Obj Y) (Diagram.reindex p q f) ≈ₐ
      Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) f := by
  subst p
  subst q
  exact SameArrow.refl _

private theorem denote_generator (e : S.Edge) :
    (Sheet.generator (S := S) e).denote E = Diagram.Presented.ofTerm
      (A := Obj (S.source e)) (B := Obj (S.target e)) (.gen e) := by
  let p := List.append_nil (S.source e)
  let q := List.append_nil (S.target e)
  have h := sheet_reindex_denote E p q (Sheet.cons (Row.box (S := S) e .empty) (.empty _))
  have hu := (term_reindex E p q (.tensor (.gen e) (.id []))).symm.trans
    (.of_eq (Quotient.sound (Diagram.Congruence.tensor_unit_right (E := E) (.gen e))))
  exact (h.trans ((SameArrow.of_eq (Category.comp_id _)).trans hu)).eq

theorem denote_encode {A B : List O} (f : Diagram S A B) :
    (Sheet.encode f).denote E = Diagram.Presented.ofTerm (A := Obj A) (B := Obj B) f := by
  induction f with
  | id A => rfl
  | gen e => exact denote_generator E e
  | comp f g hf hg =>
    simp only [Sheet.encode, denote_then E, hf, hg]
    rfl
  | tensor f g hf hg =>
    simp only [Sheet.encode, denote_tensor E, hf, hg]
    rfl

end Silmaril.RuntimeWires.Proofs.SlicedCompleteness
