module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Associator.Thms
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Associator
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Laws

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem packedArrow_lift_comp {X A B F : SynCat S}
    {a g : Tm Empty S.Instr 1} (ha : HasType S.Instr Ctx.nil (.snoc .nil X.ty) a A.ty)
    (pa : Pure S.pureEff a) (hg : HasType S.Instr Ctx.nil (.snoc .nil A.ty) g B.ty) :
    packedArrow (ha.lift (B := F.ty)) ≫ mk hg =
      packedArrow ((HasType.let₁ ha hg.underBinder).lift (B := F.ty)) := by
  let body := onNewestTyping (β := .snoc .nil X.ty) hg
  have beta := Eqv.ax (.structural (.letBeta pa)) (.let₁ ha body) (body.instantiate ha)
  have shift : underBinder g = onNewest g := rename_congr (Fin.cases rfl (fun i => i.elim0)) _
  rw [subst_onNewest, ← shift] at beta
  have e := beta.rename (TypedRenaming.succ (.snoc .nil X.ty) F.ty)
  change Eqv S.pureEff Ctx.nil _ (lift (.let₁ a (underBinder g)))
    (lift (bsubst (fun _ : Fin 1 => a) g)) B.ty at e
  have lift_sub : lift (bsubst (fun _ : Fin 1 => a) g) = bsubst (fun _ : Fin 1 => lift a) g :=
    rename_bsubst Fin.succ _ _
  rw [lift_sub] at e
  exact (packedArrow_apply ha.lift (pa.rename _) hg).trans
    ((packedArrow_eq_iff _ (applyTyping ha.lift hg)).mpr e).symm

private theorem tensorRight_after_effect {X R A B : SynCat S} {a : X ⟶ A} {g : A ⟶ B}
    (ha : IsPureMor a) (hg : IsPureMor g) (b : X ⟶ R) :
    pairArrows a b ≫ tensorRight R g = pairArrows (a ≫ g) b := by
  obtain ⟨a, ha, pa, rfl⟩ := ha
  obtain ⟨g, hg, pg, rfl⟩ := hg
  induction b using Syn.ind with
  | H b hb =>
    let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil X.ty) (A := R.ty)
    let ga := HasType.let₁ ha hg.underBinder
    have pga : Pure S.pureEff (.let₁ a (underBinder g)) := .let₁ pa (pg.rename _)
    change (mk (.pair ha hb) : X ⟶ productObj A R) ≫ tensorRight R (mk hg) =
      mk (.pair ga hb)
    rw [Syn.mk_eq_mk _ _ (pair_pure_left ha hb pa),
      Syn.mk_eq_mk _ _ (pair_pure_left ga hb pga)]
    apply after_let_from_packed hb (.pair ha.lift x) (.pair (pa.rename _) .bv)
      (.pair ga.lift x)
    change pairArrows (packedArrow ha.lift) (packedArrow x) ≫ tensorRight R (mk hg) =
      pairArrows (packedArrow ga.lift) (packedArrow x)
    exact (tensorRight_pair (R := R) (A := A) (B := B)
      (packedArrow_isPureMor ha.lift (pa.rename _)) (packedArrow_isPureMor x .bv) (mk hg)).trans
      (congrArg (fun h => pairArrows h (packedArrow x)) (packedArrow_lift_comp (F := R) ha pa hg))

private theorem pair_projections (A B : SynCat S) :
    pairArrows (first A B) (second A B) = 𝟙 (productObj A B) := by
  have e := congrArg (fun f => f.hom) (CartesianMonoidalCategory.lift_fst_snd
    (X := (⟨A⟩ : ValueCat S)) (Y := ⟨B⟩))
  rw [valueLift_hom] at e
  exact e

private theorem tensor_exchange_left {A B : SynCat S} {g : A ⟶ B}
    (hg : IsPureMor g) {X Y : SynCat S} (f : X ⟶ Y) :
    tensorRight X g ≫ tensorLeft B f = tensorLeft A f ≫ tensorRight Y g := by
  let a := first A X
  let b := second A X
  have ha : IsPureMor a := isPureMor_first A X
  have hb : IsPureMor b := isPureMor_second A X
  have e : pairArrows a b ≫ (tensorRight X g ≫ tensorLeft B f) =
      pairArrows a b ≫ (tensorLeft A f ≫ tensorRight Y g) := by
    simp only [← Category.assoc]
    rw [tensorRight_pair ha hb, tensorLeft_pair (ha.comp hg) hb, tensorLeft_pair ha hb,
      tensorRight_after_effect ha hg]
  have id : pairArrows a b = 𝟙 _ := pair_projections A X
  simpa only [id, Category.id_comp] using e

theorem pure_isCentral_proof {A B : SynCat S} {g : A ⟶ B}
    (hg : IsPureMor g) : @PremonoidalCategory.IsCentral _ _ (computationTensor S) _ _ g := by
  constructor
  · intro X Y f
    exact tensor_exchange_left hg f
  · intro X Y f
    change tensorRight A f ≫ tensorLeft Y g = tensorLeft X g ≫ tensorRight B f
    apply (cancel_mono (tensorSwap Y B).hom).1
    rw [Category.assoc, tensorSwap_naturality_right, ← Category.assoc (tensorRight A f),
      tensorSwap_naturality_left, Category.assoc, Category.assoc (tensorLeft X g),
      tensorSwap_naturality_left, ← Category.assoc (tensorLeft X g), tensorSwap_naturality_right,
      Category.assoc, tensor_exchange_left hg f]

theorem computationPentagon (W X Y Z : SynCat S) :
    @MonoidalCategory.Pentagon _ _ (computationTensor S) W X Y Z := by
  let w : ValueCat S := ⟨W⟩
  let x : ValueCat S := ⟨X⟩
  let y : ValueCat S := ⟨Y⟩
  let z : ValueCat S := ⟨Z⟩
  change tensorRight Z (tensorAssociator W X Y).hom ≫
    (tensorAssociator W (productObj X Y) Z).hom ≫ tensorLeft W (tensorAssociator X Y Z).hom = _
  have left := tensorRight_value (R := z) (α_ w x y).hom
  have right := tensorLeft_value (R := w) (α_ x y z).hom
  change tensorRight Z (tensorAssociator W X Y).hom = _ at left
  change tensorLeft W (tensorAssociator X Y Z).hom = _ at right
  rw [left, right]
  exact congrArg (fun g => g.hom) (MonoidalCategory.pentagon w x y z)

theorem computationTriangle (X Y : SynCat S) :
    (tensorAssociator X (tensorUnit S) Y).hom ≫ tensorLeft X (tensorLeftUnitor Y).hom =
      tensorRight Y (tensorRightUnitor X).hom := by
  let x : ValueCat S := ⟨X⟩
  let y : ValueCat S := ⟨Y⟩
  have left := tensorLeft_value (R := x) (λ_ y).hom
  have right := tensorRight_value (R := y) (ρ_ x).hom
  change tensorLeft X (tensorLeftUnitor Y).hom = _ at left
  change tensorRight Y (tensorRightUnitor X).hom = _ at right
  rw [left, right]
  exact congrArg (fun g => g.hom) (MonoidalCategory.triangle x y)

theorem computationHexagonForward (X Y Z : SynCat S) :
    (tensorAssociator X Y Z).hom ≫ (tensorSwap X (productObj Y Z)).hom ≫
    (tensorAssociator Y Z X).hom = tensorRight Z (tensorSwap X Y).hom ≫
      (tensorAssociator Y X Z).hom ≫ tensorLeft Y (tensorSwap X Z).hom := by
  let : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  let x : ValueCat S := ⟨X⟩
  let y : ValueCat S := ⟨Y⟩
  let z : ValueCat S := ⟨Z⟩
  have left := tensorRight_value (R := z) (BraidedCategory.braiding x y).hom
  have right := tensorLeft_value (R := y) (BraidedCategory.braiding x z).hom
  change tensorRight Z (tensorSwap X Y).hom = _ at left
  change tensorLeft Y (tensorSwap X Z).hom = _ at right
  change (tensorAssociator X Y Z).hom ≫ (tensorSwap X (productObj Y Z)).hom ≫
    (tensorAssociator Y Z X).hom = tensorRight Z (tensorSwap X Y).hom ≫
      (tensorAssociator Y X Z).hom ≫ tensorLeft Y (tensorSwap X Z).hom
  rw [left, right]
  exact congrArg (fun g => g.hom) (BraidedCategory.hexagon_forward x y z)

theorem computationHexagonReverse (X Y Z : SynCat S) :
    (tensorAssociator X Y Z).inv ≫ (tensorSwap (productObj X Y) Z).hom ≫
    (tensorAssociator Z X Y).inv = tensorLeft X (tensorSwap Y Z).hom ≫
      (tensorAssociator X Z Y).inv ≫ tensorRight Y (tensorSwap X Z).hom := by
  let : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  let x : ValueCat S := ⟨X⟩
  let y : ValueCat S := ⟨Y⟩
  let z : ValueCat S := ⟨Z⟩
  have left := tensorLeft_value (R := x) (BraidedCategory.braiding y z).hom
  have right := tensorRight_value (R := y) (BraidedCategory.braiding x z).hom
  change tensorLeft X (tensorSwap Y Z).hom = _ at left
  change tensorRight Y (tensorSwap X Z).hom = _ at right
  change (tensorAssociator X Y Z).inv ≫ (tensorSwap (productObj X Y) Z).hom ≫
    (tensorAssociator Z X Y).inv = tensorLeft X (tensorSwap Y Z).hom ≫
      (tensorAssociator X Z Y).inv ≫ tensorRight Y (tensorSwap X Z).hom
  rw [left, right]
  exact congrArg (fun g => g.hom) (BraidedCategory.hexagon_reverse x y z)

end Silmaril.Thesis.LambdaIter.Syn.SynCat
