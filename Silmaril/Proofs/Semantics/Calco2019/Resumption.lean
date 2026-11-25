module

public import Silmaril.Semantics.Calco2019.Resumption

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

variable {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}

@[reassoc]
theorem parameter_comp {U V W : C} (j : U ⟶ V) (k : V ⟶ W) (X : C) :
    (M.map (j ≫ k)).app X = (M.map j).app X ≫ (M.map k).app X := by
  rw [M.map_comp]
  rfl

theorem parameter_id (U X : C) : (M.map (𝟙 U)).app X = 𝟙 ((M.obj U).obj X) := by
  rw [M.map_id]
  rfl

@[reassoc]
theorem parameter_extend {W V X Y : C} (j : W ⟶ V) (g : X ⟶ (M.obj W).obj Y) :
    (M.parameter X).map j ≫ M.extend (W := V) (g ≫ (M.parameter Y).map j) =
      M.extend (W := W) g ≫ (M.parameter Y).map j := by
  simp only [ParametrizedMonad.parameter, ParametrizedMonad.extend, Functor.map_comp,
    Category.assoc, MonadHom.app_μ]
  rw [← (M.map j).toNatTrans.naturality_assoc g,
    ← (M.map j).toNatTrans.naturality_assoc ((M.map j).app Y)]

variable (R : FinalResumptions M)

@[reassoc]
theorem unfold_spec {X S : C} (b : S ⟶ (M.obj S).obj X) :
    R.unfold b ≫ R.out X = b ≫ (M.parameter X).map (R.unfold b) :=
  ((R.final X).from (⟨S, b⟩ : Coalgebra (M.parameter X))).h.symm

theorem unfold_unique {X S : C} (b : S ⟶ (M.obj S).obj X) (q : S ⟶ R.obj X)
    (h : q ≫ R.out X = b ≫ (M.parameter X).map q) : q = R.unfold b :=
  congrArg Coalgebra.Hom.f ((R.final X).hom_ext (⟨q, h.symm⟩ :
    (⟨S, b⟩ : Coalgebra (M.parameter X)) ⟶ R.coalgebra X) _)

theorem out_roll (X : C) : R.out X ≫ R.roll X = 𝟙 (R.obj X) :=
  Coalgebra.Terminal.right_inv (R.final X)

theorem roll_out (X : C) : R.roll X ≫ R.out X = 𝟙 ((M.obj (R.obj X)).obj X) :=
  Coalgebra.Terminal.left_inv (R.final X)

variable (P : Coproducts C)

theorem extend_spec_unique {X Y : C} (f : X ⟶ R.obj Y) :
    R.IsExtension f (R.extend P f) ∧ ∀ k, R.IsExtension f k → k = R.extend P f := by
  let S := P.sum (R.obj X) (R.obj Y)
  let b := R.extensionBody P f
  let q := R.unfold b
  have qRight : P.inr (X := R.obj X) ≫ q = 𝟙 (R.obj Y) := by
    trans R.unfold (R.out Y)
    · apply unfold_unique
      simp only [Category.assoc, q, unfold_spec R, b, FinalResumptions.extensionBody, P.inr_desc_assoc]
      rw [← parameter_comp]
    · symm
      exact unfold_unique R _ _ (by simp)
  have leftBody (m : S ⟶ R.obj Y) (hm : P.inr (X := R.obj X) ≫ m = 𝟙 (R.obj Y)) :
      P.inl ≫ b ≫ (M.parameter Y).map m =
        R.out X ≫ (M.parameter X).map (P.inl ≫ m) ≫ M.extend (W := R.obj Y) (f ≫ R.out Y) := by
    simp only [b, FinalResumptions.extensionBody, P.inl_desc_assoc, Category.assoc]
    rw [← parameter_extend (M := M) m (f ≫ R.out Y ≫ (M.parameter Y).map P.inr)]
    simp only [Category.assoc, ← parameter_comp_assoc, ← parameter_comp, hm, parameter_id,
      Category.comp_id]
  refine ⟨?_, ?_⟩
  · change (P.inl ≫ q) ≫ R.out Y = _
    rw [Category.assoc, unfold_spec]
    exact leftBody q qRight
  · intro k hk
    change k ≫ R.out Y = _ at hk
    let m : S ⟶ R.obj Y := P.desc k (𝟙 _)
    have hm : m = q := by
      apply unfold_unique R b m
      apply P.hom_ext
      · rw [← Category.assoc, P.inl_desc, leftBody m (P.inr_desc _ _), P.inl_desc]
        exact hk
      · simp only [b, FinalResumptions.extensionBody, m, P.inr_desc_assoc, Category.id_comp, Category.assoc,
          ← parameter_comp, P.inr_desc, parameter_id, Category.comp_id]
    exact (P.inl_desc k (𝟙 _)).symm.trans (congrArg (fun j => P.inl ≫ j) hm)

@[reassoc]
theorem extend_spec {X Y : C} (f : X ⟶ R.obj Y) :
    R.extend P f ≫ R.out Y =
      R.out X ≫ (M.parameter X).map (R.extend P f) ≫ M.extend (f ≫ R.out Y) :=
  (extend_spec_unique R P f).1

theorem extend_unique {X Y : C} (f : X ⟶ R.obj Y) (k : R.obj X ⟶ R.obj Y)
    (hk : R.IsExtension f k) : k = R.extend P f :=
  (extend_spec_unique R P f).2 k hk

@[reassoc]
theorem unit_out (X : C) : R.unit X ≫ R.out X = (M.obj (R.obj X)).η.app X := by
  simp [FinalResumptions.unit, roll_out R]

@[reassoc]
theorem parameter_unit {W V : C} (j : W ⟶ V) (Y : C) :
    (M.obj W).η.app Y ≫ (M.parameter Y).map j = (M.obj V).η.app Y :=
  (M.map j).app_η Y

private theorem solution_factor {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y)
    (g : X ⟶ R.obj Y) (q : R.obj (P.sum Y X) ⟶ R.obj Y)
    (hg : g ≫ R.out Y = f ≫ (M.parameter Y).map q) :
    (M.parameter (P.sum Y X)).map q ≫ M.extend (P.desc (R.unit Y) g ≫ R.out Y) =
      M.extend (W := R.obj (P.sum Y X)) (P.desc ((M.obj (R.obj (P.sum Y X))).η.app Y) f) ≫
        (M.parameter Y).map q := by
  have h : P.desc (R.unit Y) g ≫ R.out Y =
      P.desc ((M.obj (R.obj (P.sum Y X))).η.app Y) f ≫ (M.parameter Y).map q := by
    simp [unit_out R, hg]
  rw [h, parameter_extend]

theorem solve_spec_unique {X Y : C} (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y) :
    R.IsSolution P f (R.solve P f) ∧
      ∀ g, R.IsSolution P f g → g = R.solve P f := by
  let b := R.solutionBody P f
  let q := R.unfold b
  let g := R.solve P f
  have hg : g ≫ R.out Y = f ≫ (M.parameter Y).map q := by
    simp [g, FinalResumptions.solve, q, b, roll_out R]
  have hq : q = R.extend P (P.desc (R.unit Y) g) := by
    apply extend_unique
    dsimp only [FinalResumptions.IsExtension]
    rw [solution_factor R P f g q hg]
    simpa [q, b, FinalResumptions.solutionBody, Category.assoc] using unfold_spec R b
  refine ⟨?_, ?_⟩
  · exact hg.trans (congrArg (fun k => f ≫ (M.parameter Y).map k) hq)
  · rintro k hk
    let m := R.extend P (P.desc (R.unit Y) k)
    have hm : m = q := by
      apply unfold_unique
      simp only [m, extend_spec R, solution_factor R P f k m hk, b,
        FinalResumptions.solutionBody, Category.assoc]
    have heq : k ≫ R.out Y = g ≫ R.out Y :=
      (hk : k ≫ R.out Y = _).trans ((congrArg (fun j => f ≫ (M.parameter Y).map j) hm).trans hg.symm)
    simpa [Category.assoc, out_roll R] using congrArg (fun j => j ≫ R.roll Y) heq

private theorem out_cancel {X Y : C} {g h : X ⟶ R.obj Y}
    (e : g ≫ R.out Y = h ≫ R.out Y) : g = h := by
  simpa [out_roll R] using congrArg (fun f => f ≫ R.roll Y) e

@[reassoc]
private theorem monad_unit_extend {W X Y : C} (f : X ⟶ (M.obj W).obj Y) :
    (M.obj W).η.app X ≫ M.extend f = f := by
  rw [ParametrizedMonad.extend, ← (M.obj W).η.naturality_assoc, (M.obj W).left_unit]
  exact Category.comp_id f

private theorem monad_extend_unit (W X : C) :
    M.extend ((M.obj W).η.app X) = 𝟙 ((M.obj W).obj X) :=
  (M.obj W).right_unit X

@[reassoc]
private theorem monad_extend_comp {W X Y Z : C}
    (f : X ⟶ (M.obj W).obj Y) (g : Y ⟶ (M.obj W).obj Z) :
    M.extend f ≫ M.extend g = M.extend (f ≫ M.extend g) := by
  simp only [ParametrizedMonad.extend, Category.assoc, Functor.map_comp]
  rw [← (M.obj W).μ.naturality_assoc g, (M.obj W).assoc]
  rfl

@[reassoc]
theorem unit_extend {X Y : C} (f : X ⟶ R.obj Y) :
    R.unit X ≫ R.extend P f = f := by
  apply out_cancel R
  rw [Category.assoc, extend_spec R, unit_out_assoc R, parameter_unit_assoc, monad_unit_extend]

theorem extend_unit (X : C) : R.extend P (R.unit X) = 𝟙 (R.obj X) := by
  symm
  apply extend_unique R P
  simp only [FinalResumptions.IsExtension, Category.id_comp, parameter_id, unit_out R,
    monad_extend_unit, Category.comp_id]

theorem extend_comp {X Y Z : C} (f : X ⟶ R.obj Y) (g : Y ⟶ R.obj Z) :
    R.extend P f ≫ R.extend P g = R.extend P (f ≫ R.extend P g) := by
  apply extend_unique R P
  dsimp only [FinalResumptions.IsExtension]
  let k := R.extend P f
  let l := R.extend P g
  have hl : l ≫ R.out Z = R.out Y ≫ (M.parameter Y).map l ≫ M.extend (g ≫ R.out Z) :=
    extend_spec R P g
  change (k ≫ l) ≫ R.out Z =
    R.out X ≫ (M.parameter X).map (k ≫ l) ≫ M.extend ((f ≫ l) ≫ R.out Z)
  calc
    (k ≫ l) ≫ R.out Z =
        R.out X ≫ (M.parameter X).map k ≫
          (M.extend (f ≫ R.out Y) ≫ (M.parameter Y).map l) ≫ M.extend (g ≫ R.out Z) := by
      simp only [Category.assoc, l, k, extend_spec R, extend_spec_assoc R]
    _ = R.out X ≫ (M.parameter X).map (k ≫ l) ≫
        M.extend ((f ≫ R.out Y ≫ (M.parameter Y).map l) ≫ M.extend (g ≫ R.out Z)) := by
      rw [← parameter_extend, Category.assoc, Category.assoc, ← parameter_comp_assoc,
        monad_extend_comp]
    _ = _ := by simp only [Category.assoc, hl]

end Silmaril.Calco2019.Proofs
