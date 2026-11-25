module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.OrdinarySquare.Defs

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation
open ContinuationContext (single)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "F" => toInterface (τ := τ) Φ
local notation "N" => Paper.fromNative (Φ := Φ) (Γ := ([] : VCtx τ))

set_option backward.isDefEq.respectTransparency false

@[reassoc]
private theorem pack_repeat (A B : τ) :
    (N).map ((single A).appendInl (single B)) ≫ packStepExits (Φ := Φ) A B =
      (F).map (coprod.inr : ofType A ⟶ ofType B ⨿ ofType A) :=
  (appendIsColimit (Φ := Φ) (Γ := []) (single A) (single B)).fac
    (BinaryCofan.mk ((F).map coprod.inr) ((F).map coprod.inl)) ⟨.left⟩

@[reassoc]
private theorem pack_outward (A B : τ) :
    (N).map ((single A).appendInr (single B)) ≫ packStepExits (Φ := Φ) A B =
      (F).map (coprod.inl : ofType B ⟶ ofType B ⨿ ofType A) :=
  (appendIsColimit (Φ := Φ) (Γ := []) (single A) (single B)).fac
    (BinaryCofan.mk ((F).map coprod.inr) ((F).map coprod.inl)) ⟨.right⟩

private noncomputable def unpack (A B : τ) :
    (F).obj (ofType B ⨿ ofType A) ⟶ (N).obj ((single A).append (single B)) :=
  (F).map (sumIso (Φ := Φ) B A).inv ≫ (singletonSumIsColimit (Φ := Φ) (Γ := []) B A).desc
    (BinaryCofan.mk ((N).map ((single A).appendInr (single B)))
      ((N).map ((single A).appendInl (single B))))

private theorem unpack_repeat (A B : τ) :
    (F).map (coprod.inr : ofType A ⟶ ofType B ⨿ ofType A) ≫ unpack (Φ := Φ) A B =
      (N).map ((single A).appendInl (single B)) := by
  rw [unpack, ← (F).map_comp_assoc, ← sumCofan_inr_sumIso_hom B A, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact (singletonSumIsColimit (Φ := Φ) (Γ := []) B A).fac _ ⟨.right⟩

private theorem unpack_outward (A B : τ) :
    (F).map (coprod.inl : ofType B ⟶ ofType B ⨿ ofType A) ≫ unpack (Φ := Φ) A B =
      (N).map ((single A).appendInr (single B)) := by
  rw [unpack, ← (F).map_comp_assoc, ← sumCofan_inl_sumIso_hom B A, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact (singletonSumIsColimit (Φ := Φ) (Γ := []) B A).fac _ ⟨.left⟩

private theorem pack_unpack (A B : τ) :
    packStepExits (Φ := Φ) A B ≫ unpack (Φ := Φ) A B = 𝟙 _ := by
  apply append_hom_ext (single A) (single B)
  · rw [pack_repeat_assoc, unpack_repeat, Category.comp_id]
  · rw [pack_outward_assoc, unpack_outward, Category.comp_id]

private theorem pack_mono (A B : τ) : Mono (packStepExits (Φ := Φ) A B) :=
  ⟨fun _ _ h => by
    simpa only [Category.assoc, pack_unpack, Category.comp_id] using
      congrArg (fun f => f ≫ unpack (Φ := Φ) A B) h⟩

variable {A B D : τ} {t : Tm Φ} {p q : Region Φ}

private def localChange (B : τ) (ht : Tm.HasType [A] t D) :
    (N).obj ((single A).append (single B)) ⟶
      (N).obj ((single D).append (single B)) :=
  toHom (Φ := Φ) (Γ := []) ⟨boundLocalMap t, by
    intro i T hi
    change At [A, B] i T at hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .let₁ ht (.br (ℓ := 0) rfl (.var (i := 0) rfl))
    | succ i => exact .br (ℓ := i + 1) hi (.var (i := 0) rfl)⟩

@[reassoc]
private theorem localChange_repeat (ht : Tm.HasType [A] t D) :
    (N).map ((single A).appendInl (single B)) ≫ localChange B ht =
      (F).map (boundReturn ht) ≫ (N).map ((single D).appendInl (single B)) := by
  apply (toHom_eq_iff (Φ := Φ) (Γ := [])).mpr
  intro i T hi
  change At [A] i T at hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    change Paper.Eqv [A] (compLSubst labelId (boundLocalMap t) 0)
      (compLSubst (fun _ => (Region.br 0 t).bindBranchArguments) labelId 0) [D, B]
    rw [compLSubst_id_left, compLSubst_id_right]
    exact .refl (.let₁ ht (.br (ℓ := 0) rfl (.var (i := 0) rfl)))
  | succ i => simp [At] at hi

@[reassoc]
private theorem localChange_outward (ht : Tm.HasType [A] t D) :
    (N).map ((single A).appendInr (single B)) ≫ localChange B ht =
      (N).map ((single D).appendInr (single B)) := by
  apply (toHom_eq_iff (Φ := Φ) (Γ := [])).mpr
  intro i T hi
  change At [B] i T at hi
  change Paper.Eqv [T] (compLSubst labelId (boundLocalMap t) (1 + i))
    (labelId (1 + i)) [D, B]
  rw [compLSubst_id_left, Nat.one_add]
  exact .refl (.br (ℓ := i + 1) hi (.var (i := 0) rfl))

private theorem pack_localChange (ht : Tm.HasType [A] t D) :
    packStepExits A B ≫ (F).map (coprod.map (𝟙 (ofType B)) (boundReturn ht)) =
      localChange B ht ≫ packStepExits D B := by
  apply append_hom_ext (single A) (single B)
  · rw [pack_repeat_assoc, ← (F).map_comp, coprod.inr_map, (F).map_comp, localChange_repeat_assoc,
      pack_repeat]
  · rw [pack_outward_assoc, ← (F).map_comp, coprod.inl_map, Category.id_comp,
      localChange_outward_assoc, pack_outward]

private theorem arrow_square_iff (hp : ValueBranches [A] p [A, B])
    (hq : ValueBranches [D] q [D, B]) (ht : Tm.HasType [A] t D) :
    stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (boundReturn ht) =
        boundReturn ht ≫ stepArrow hq ↔
      Paper.singletonArrow hp ≫ localChange B ht = (F).map (boundReturn ht) ≫ Paper.singletonArrow hq := by
  have left : (F).map (stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (boundReturn ht)) =
      (Paper.singletonArrow hp ≫ localChange B ht) ≫ packStepExits D B := by
    rw [(F).map_comp]
    change (Paper.singletonArrow hp ≫ packStepExits A B) ≫ _ = _
    rw [Category.assoc, pack_localChange, Category.assoc]
  have right : (F).map (boundReturn ht ≫ stepArrow hq) =
      ((F).map (boundReturn ht) ≫ Paper.singletonArrow hq) ≫ packStepExits D B := by
    rw [(F).map_comp]
    exact (Category.assoc _ _ _).symm
  let : Mono (packStepExits (Φ := Φ) D B) := pack_mono D B
  constructor
  · intro comm
    apply (cancel_mono (packStepExits D B)).1
    rw [← left, ← right, comm]
  · intro square
    apply (F).map_injective
    rw [left, right, square]

theorem ordinary_square_iff (hp : ValueBranches [A] p [A, B])
    (hq : ValueBranches [D] q [D, B]) (ht : Tm.HasType [A] t D) :
    stepArrow hp ≫ coprod.map (𝟙 (ofType B)) (boundReturn ht) =
        boundReturn ht ≫ stepArrow hq ↔
      Paper.Eqv [A] (p.lsubst (liftLSubstVars (boundLocalMap t)))
        ((Region.br 0 t).bindBranchArguments.lsubst (liftLSubstVars (fun _ => q))) [D, B] := by
  rw [arrow_square_iff hp hq ht]
  constructor
  · intro sq
    exact (toHom_eq_iff (Φ := Φ) (Γ := [])).mp sq (i := 0) (A := A) rfl
  · intro sq
    apply (toHom_eq_iff (Φ := Φ) (Γ := [])).mpr
    intro i T hi
    change At [A] i T at hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact sq
    | succ i => simp [At] at hi

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundOrdinarySquare
