module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Laws

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem instantiate_underBinder {n : Nat} {p : Tm Empty S.Instr (n + 1)}
    (a : Tm Empty S.Instr (n + 1)) :
    instantiate (underBinder p) a = bsubst (Fin.cases a (fun i => .bv i.succ)) p := by
  rw [instantiate, underBinder, bsubst_rename]
  exact bsubst_congr (Fin.cases rfl (fun _ => rfl)) _

private theorem keep_lift {n : Nat} (a : Tm Empty S.Instr (n + 1)) (b : Tm Empty S.Instr n) :
    bsubst (Fin.cases a (fun i => .bv i.succ)) (lift b) = lift b := by
  rw [lift, bsubst_rename]
  exact bsubst_bv_eq_rename Fin.succ b

private theorem pair_let_left {n : Nat} {β : BoundCtx S.Ty n} {F A B : S.Ty}
    {f b : Tm Empty S.Instr n} {a : Tm Empty S.Instr (n + 1)}
    (hf : HasType S.Instr Ctx.nil β f F) (ha : HasType S.Instr Ctx.nil (.snoc β F) a A)
    (hb : HasType S.Instr Ctx.nil β b B) (hpa : Pure S.pureEff a) (hpb : Pure S.pureEff b) :
    Eqv S.pureEff Ctx.nil β (.pair (.let₁ f a) b)
      (.let₁ f (.pair a (lift b))) (tensor A B) := by
  let q := HasType.pair (HasType.newest (A := A)) hb.lift
  let g := HasType.let₁ hf ha
  have seq := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
    (.let₁ g q) (.let₁ hf (.let₁ ha q.underBinder))
  have beta := Eqv.ax (.structural (.letBeta hpa)) (.let₁ ha q.underBinder)
    (q.underBinder.instantiate ha)
  rw [instantiate_underBinder, bsubst_pair, bsubst_bv, Fin.cases_zero, keep_lift] at beta
  exact (pair_pure_right g hb hpb).trans (seq.trans (.let₁ (.refl hf) beta))

private theorem pair_let_right {n : Nat} {β : BoundCtx S.Ty n} {F A B : S.Ty}
    {a f : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A) (hf : HasType S.Instr Ctx.nil β f F)
    (hb : HasType S.Instr Ctx.nil (.snoc β F) b B)
    (hpa : Pure S.pureEff a) (hpb : Pure S.pureEff b) :
    Eqv S.pureEff Ctx.nil β (.pair a (.let₁ f b))
      (.let₁ f (.pair (lift a) b)) (tensor A B) := by
  let q := HasType.pair ha.lift (HasType.newest (A := B))
  let g := HasType.let₁ hf hb
  have seq := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
    (.let₁ g q) (.let₁ hf (.let₁ hb q.underBinder))
  have beta := Eqv.ax (.structural (.letBeta hpb)) (.let₁ hb q.underBinder)
    (q.underBinder.instantiate hb)
  rw [instantiate_underBinder, bsubst_pair, bsubst_bv, Fin.cases_zero, keep_lift] at beta
  exact (pair_pure_left ha g hpa).trans (seq.trans (.let₁ (.refl hf) beta))

private theorem subst_onNewest {n : Nat} (p : Tm Empty S.Instr n) (k : Tm Empty S.Instr 1) :
    instantiate (onNewest k) p = bsubst (fun _ => p) k := by
  rw [instantiate, onNewest, bsubst_rename]
  rfl

private def applyTyping {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {p : Tm Empty S.Instr n} {k : Tm Empty S.Instr 1}
    (hp : HasType S.Instr Ctx.nil β p A) (hk : HasType S.Instr Ctx.nil (.snoc .nil A) k B) :
    HasType S.Instr Ctx.nil β (bsubst (fun _ => p) k) B :=
  hk.bsubst (fun i => Fin.cases hp (fun j => j.elim0) i)

private theorem packedArrow_apply {n : Nat} {β : BoundCtx S.Ty n} {A B : SynCat S}
    {p : Tm Empty S.Instr n} {k : Tm Empty S.Instr 1}
    (hp : HasType S.Instr Ctx.nil β p A.ty) (pure : Pure S.pureEff p)
    (hk : HasType S.Instr Ctx.nil (.snoc .nil A.ty) k B.ty) :
    packedArrow hp ≫ mk hk = packedArrow (applyTyping hp hk) := by
  have pPacked := packedTerm_pure β pure
  let hp' := packedTyping hp
  let hk' := onNewestTyping (β := .snoc .nil (packType β)) hk
  have e := Eqv.ax (.structural (.letBeta pPacked)) (.let₁ hp' hk') (hk'.instantiate hp')
  rw [subst_onNewest] at e
  apply Quotient.sound
  change Eqv S.pureEff Ctx.nil _ (.let₁ (packedTerm β p) (underBinder k))
    (packedTerm β (bsubst (fun _ : Fin 1 => p) k)) B.ty
  have shift : underBinder k = onNewest k :=
    rename_congr (Fin.cases rfl (fun i => i.elim0)) _
  have packed_apply : packedTerm β (bsubst (fun _ : Fin 1 => p) k) =
      bsubst (fun _ : Fin 1 => packedTerm β p) k :=
    bsubst_comp _ _ _
  rw [shift, packed_apply]
  exact e

private theorem after_let_from_packed {X F A B : SynCat S} {f : Tm Empty S.Instr 1}
    {p q : Tm Empty S.Instr 2} (hf : HasType S.Instr Ctx.nil (.snoc .nil X.ty) f F.ty)
    (hp : HasType S.Instr Ctx.nil (.snoc (.snoc .nil X.ty) F.ty) p A.ty)
    (pure : Pure S.pureEff p)
    (hq : HasType S.Instr Ctx.nil (.snoc (.snoc .nil X.ty) F.ty) q B.ty)
    (k : A ⟶ B) (e : packedArrow hp ≫ k = packedArrow hq) :
    (mk (.let₁ hf hp) : X ⟶ A) ≫ k = (mk (.let₁ hf hq) : X ⟶ B) := by
  induction k using Syn.ind with
  | H k hk =>
    let body := onNewestTyping (β := .snoc .nil X.ty) hk
    have shift₁ : underBinder k = onNewest k := rename_congr (Fin.cases rfl (fun i => i.elim0)) _
    have shift₂ : underBinder (onNewest (n := 1) k) = onNewest k := by
      rw [underBinder, onNewest, onNewest, rename_comp]
      exact rename_congr (fun _ => rfl) _
    have step := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
      (.let₁ (.let₁ hf hp) body) (.let₁ hf (.let₁ hp body.underBinder))
    rw [shift₂] at step
    let body' := onNewestTyping (β := .snoc (.snoc .nil X.ty) F.ty) hk
    have beta := Eqv.ax (.structural (.letBeta pure)) (.let₁ hp body') (body'.instantiate hp)
    rw [subst_onNewest] at beta
    have tail := (packedArrow_eq_iff (applyTyping hp hk) hq).mp
      ((packedArrow_apply hp pure hk).symm.trans e)
    apply Quotient.sound
    change Eqv S.pureEff Ctx.nil _ (.let₁ (.let₁ f p) (underBinder k)) (.let₁ f q) B.ty
    rw [shift₁]
    exact step.trans (.let₁ (.refl hf) (beta.trans tail))

private theorem assoc_pair_pure {X A B C : SynCat S} {a : X ⟶ A} {b : X ⟶ B} {c : X ⟶ C}
    (ha : IsPureMor a) (hb : IsPureMor b) (hc : IsPureMor c) :
    pairArrows (pairArrows a b) c ≫ (tensorAssociator A B C).hom =
      pairArrows a (pairArrows b c) := by
  let av : (⟨X⟩ : ValueCat S) ⟶ ⟨A⟩ := ⟨a, ha⟩
  let bv : (⟨X⟩ : ValueCat S) ⟶ ⟨B⟩ := ⟨b, hb⟩
  let cv : (⟨X⟩ : ValueCat S) ⟶ ⟨C⟩ := ⟨c, hc⟩
  have e := congrArg (fun g => g.hom)
    (CartesianMonoidalCategory.lift_lift_associator_hom av bv cv)
  change (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.lift av bv) cv).hom ≫
    (tensorAssociator A B C).hom = (CartesianMonoidalCategory.lift av (CartesianMonoidalCategory.lift bv cv)).hom at e
  rw [valueLift_hom, valueLift_hom, valueLift_hom, valueLift_hom] at e
  exact e

private theorem swap_pair_pure {X A B : SynCat S} {a : X ⟶ A} {b : X ⟶ B}
    (ha : IsPureMor a) (hb : IsPureMor b) :
    pairArrows a b ≫ (tensorSwap A B).hom = pairArrows b a := by
  let : BraidedCategory (ValueCat S) := BraidedCategory.ofCartesianMonoidalCategory
  let av : (⟨X⟩ : ValueCat S) ⟶ ⟨A⟩ := ⟨a, ha⟩
  let bv : (⟨X⟩ : ValueCat S) ⟶ ⟨B⟩ := ⟨b, hb⟩
  have e := congrArg (fun g => g.hom)
    (CartesianMonoidalCategory.lift_braiding_hom av bv)
  change (CartesianMonoidalCategory.lift av bv).hom ≫ (tensorSwap A B).hom =
    (CartesianMonoidalCategory.lift bv av).hom at e
  rw [valueLift_hom, valueLift_hom] at e
  exact e

private theorem assoc_after_let {X F A B C : SynCat S} {f : Tm Empty S.Instr 1}
    {a b c : Tm Empty S.Instr 2} (hf : HasType S.Instr Ctx.nil (.snoc .nil X.ty) f F.ty)
    (ha : HasType S.Instr Ctx.nil (.snoc (.snoc .nil X.ty) F.ty) a A.ty)
    (hb : HasType S.Instr Ctx.nil (.snoc (.snoc .nil X.ty) F.ty) b B.ty)
    (hc : HasType S.Instr Ctx.nil (.snoc (.snoc .nil X.ty) F.ty) c C.ty)
    (pa : Pure S.pureEff a) (pb : Pure S.pureEff b) (pc : Pure S.pureEff c) :
    (mk (.let₁ hf (.pair (.pair ha hb) hc)) : X ⟶ productObj (productObj A B) C) ≫
      (tensorAssociator A B C).hom = mk (.let₁ hf (.pair ha (.pair hb hc))) :=
  after_let_from_packed hf _ (.pair (.pair pa pb) pc) _ _
    (assoc_pair_pure (packedArrow_isPureMor ha pa)
      (packedArrow_isPureMor hb pb) (packedArrow_isPureMor hc pc))

private theorem assoc_pair_left {X A B C : SynCat S}
    (a : X ⟶ A) {b : X ⟶ B} {c : X ⟶ C} (hb : IsPureMor b) (hc : IsPureMor c) :
    pairArrows (pairArrows a b) c ≫ (tensorAssociator A B C).hom =
      pairArrows a (pairArrows b c) := by
  obtain ⟨b, hb, pb, rfl⟩ := hb
  obtain ⟨c, hc, pc, rfl⟩ := hc
  induction a using Syn.ind with
  | H a ha =>
    let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil X.ty) (A := A.ty)
    have left := (Eqv.pair (pair_pure_right ha hb pb) (.refl hc)).trans
      (pair_let_left ha (.pair x hb.lift) hc (.pair .bv (pb.rename _)) pc)
    have right := pair_pure_right ha (.pair hb hc) (.pair pb pc)
    change (mk (.pair (.pair ha hb) hc) : X ⟶ productObj (productObj A B) C) ≫
      (tensorAssociator A B C).hom = mk (.pair ha (.pair hb hc))
    rw [Syn.mk_eq_mk _ _ left, Syn.mk_eq_mk _ _ right]
    exact assoc_after_let ha x hb.lift hc.lift .bv (pb.rename _) (pc.rename _)

private theorem assoc_pair_middle {X A B C : SynCat S}
    {a : X ⟶ A} (ha : IsPureMor a) (b : X ⟶ B) {c : X ⟶ C} (hc : IsPureMor c) :
    pairArrows (pairArrows a b) c ≫ (tensorAssociator A B C).hom =
      pairArrows a (pairArrows b c) := by
  obtain ⟨a, ha, pa, rfl⟩ := ha
  obtain ⟨c, hc, pc, rfl⟩ := hc
  induction b using Syn.ind with
  | H b hb =>
    let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil X.ty) (A := B.ty)
    have left := (Eqv.pair (pair_pure_left ha hb pa) (.refl hc)).trans
      (pair_let_left hb (.pair ha.lift x) hc (.pair (pa.rename _) .bv) pc)
    have right := (Eqv.pair (.refl ha) (pair_pure_right hb hc pc)).trans
      (pair_let_right ha hb (.pair x hc.lift) pa (.pair .bv (pc.rename _)))
    change (mk (.pair (.pair ha hb) hc) : X ⟶ productObj (productObj A B) C) ≫
      (tensorAssociator A B C).hom = mk (.pair ha (.pair hb hc))
    rw [Syn.mk_eq_mk _ _ left, Syn.mk_eq_mk _ _ right]
    exact assoc_after_let hb ha.lift x hc.lift (pa.rename _) .bv (pc.rename _)

private theorem assoc_pair_right {X A B C : SynCat S}
    {a : X ⟶ A} {b : X ⟶ B} (ha : IsPureMor a) (hb : IsPureMor b) (c : X ⟶ C) :
    pairArrows (pairArrows a b) c ≫ (tensorAssociator A B C).hom =
      pairArrows a (pairArrows b c) := by
  obtain ⟨a, ha, pa, rfl⟩ := ha
  obtain ⟨b, hb, pb, rfl⟩ := hb
  induction c using Syn.ind with
  | H c hc =>
    let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil X.ty) (A := C.ty)
    have left := pair_pure_left (.pair ha hb) hc (.pair pa pb)
    have right := (Eqv.pair (.refl ha) (pair_pure_left hb hc pb)).trans
      (pair_let_right ha hc (.pair hb.lift x) pa (.pair (pb.rename _) .bv))
    change (mk (.pair (.pair ha hb) hc) : X ⟶ productObj (productObj A B) C) ≫
      (tensorAssociator A B C).hom = mk (.pair ha (.pair hb hc))
    rw [Syn.mk_eq_mk _ _ left, Syn.mk_eq_mk _ _ right]
    exact assoc_after_let hc ha.lift hb.lift x (pa.rename _) (pb.rename _) .bv

private theorem swap_pair {X A B : SynCat S} {a : X ⟶ A} (ha : IsPureMor a) (b : X ⟶ B) :
    pairArrows a b ≫ (tensorSwap A B).hom = pairArrows b a := by
  obtain ⟨a, ha, pa, rfl⟩ := ha
  induction b using Syn.ind with
  | H b hb =>
    let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil X.ty) (A := B.ty)
    change (mk (.pair ha hb) : X ⟶ productObj A B) ≫ (tensorSwap A B).hom = mk (.pair hb ha)
    rw [Syn.mk_eq_mk _ _ (pair_pure_left ha hb pa), Syn.mk_eq_mk _ _ (pair_pure_right hb ha pa)]
    exact after_let_from_packed hb (.pair ha.lift x) (.pair (pa.rename _) .bv) (.pair x ha.lift) _
      (swap_pair_pure (packedArrow_isPureMor ha.lift (pa.rename _)) (packedArrow_isPureMor x .bv))

private theorem tensorRight_pair {X R A B : SynCat S} {a : X ⟶ A} {b : X ⟶ R}
    (ha : IsPureMor a) (hb : IsPureMor b) (f : A ⟶ B) :
    pairArrows a b ≫ tensorRight R f = pairArrows (a ≫ f) b := by
  rw [tensorRight, ← Category.assoc, ← Category.assoc, swap_pair ha b,
    tensorLeft_pair hb ha, tensorSwap_inv, swap_pair hb]

private theorem triple_eta (A B C : SynCat S) :
    pairArrows
      (pairArrows (first (productObj A B) C ≫ first A B)
        (first (productObj A B) C ≫ second A B))
      (second (productObj A B) C) = 𝟙 _ := by
  let av : ValueCat S := ⟨A⟩
  let bv : ValueCat S := ⟨B⟩
  let cv : ValueCat S := ⟨C⟩
  let p := CartesianMonoidalCategory.fst (av ⊗ bv) cv
  have inner : CartesianMonoidalCategory.lift (p ≫ CartesianMonoidalCategory.fst av bv)
      (p ≫ CartesianMonoidalCategory.snd av bv) = p := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e := congrArg (fun g => g.hom)
    (show CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.lift (p ≫ CartesianMonoidalCategory.fst av bv)
        (p ≫ CartesianMonoidalCategory.snd av bv))
      (CartesianMonoidalCategory.snd (av ⊗ bv) cv) = 𝟙 _ by rw [inner]; simp [p])
  rw [valueLift_hom, valueLift_hom] at e
  exact e

theorem tensorAssociator_naturality_left_proof {A A' : SynCat S} (f : A ⟶ A') (B C : SynCat S) :
    tensorRight C (tensorRight B f) ≫ (tensorAssociator A' B C).hom =
      (tensorAssociator A B C).hom ≫ tensorRight (productObj B C) f := by
  let a := first (productObj A B) C ≫ first A B
  let b := first (productObj A B) C ≫ second A B
  let c := second (productObj A B) C
  have ha : IsPureMor a := (isPureMor_first _ _).comp (isPureMor_first _ _)
  have hb : IsPureMor b := (isPureMor_first _ _).comp (isPureMor_second _ _)
  have hc : IsPureMor c := isPureMor_second _ _
  have e : pairArrows (pairArrows a b) c ≫
      (tensorRight C (tensorRight B f) ≫ (tensorAssociator A' B C).hom) =
      pairArrows (pairArrows a b) c ≫
      ((tensorAssociator A B C).hom ≫ tensorRight (productObj B C) f) := by
    simp only [← Category.assoc]
    rw [tensorRight_pair (isPureMor_pairArrows ha hb) hc, tensorRight_pair ha hb,
      assoc_pair_left _ hb hc, assoc_pair_pure ha hb hc,
      tensorRight_pair ha (isPureMor_pairArrows hb hc)]
  have id : pairArrows (pairArrows a b) c = 𝟙 _ := triple_eta A B C
  simpa only [id, Category.id_comp] using e

theorem tensorAssociator_naturality_middle_proof (A : SynCat S) {B B' : SynCat S}
    (f : B ⟶ B') (C : SynCat S) :
    tensorRight C (tensorLeft A f) ≫ (tensorAssociator A B' C).hom =
      (tensorAssociator A B C).hom ≫ tensorLeft A (tensorRight C f) := by
  let a := first (productObj A B) C ≫ first A B
  let b := first (productObj A B) C ≫ second A B
  let c := second (productObj A B) C
  have ha : IsPureMor a := (isPureMor_first _ _).comp (isPureMor_first _ _)
  have hb : IsPureMor b := (isPureMor_first _ _).comp (isPureMor_second _ _)
  have hc : IsPureMor c := isPureMor_second _ _
  have e : pairArrows (pairArrows a b) c ≫
      (tensorRight C (tensorLeft A f) ≫ (tensorAssociator A B' C).hom) =
      pairArrows (pairArrows a b) c ≫
      ((tensorAssociator A B C).hom ≫ tensorLeft A (tensorRight C f)) := by
    simp only [← Category.assoc]
    rw [tensorRight_pair (isPureMor_pairArrows ha hb) hc, tensorLeft_pair ha hb,
      assoc_pair_middle ha _ hc, assoc_pair_pure ha hb hc,
      tensorLeft_pair ha (isPureMor_pairArrows hb hc), tensorRight_pair hb hc]
  have id : pairArrows (pairArrows a b) c = 𝟙 _ := triple_eta A B C
  simpa only [id, Category.id_comp] using e

theorem tensorAssociator_naturality_right_proof (A B : SynCat S) {C C' : SynCat S}
    (f : C ⟶ C') :
    tensorLeft (productObj A B) f ≫ (tensorAssociator A B C').hom =
      (tensorAssociator A B C).hom ≫ tensorLeft A (tensorLeft B f) := by
  let a := first (productObj A B) C ≫ first A B
  let b := first (productObj A B) C ≫ second A B
  let c := second (productObj A B) C
  have ha : IsPureMor a := (isPureMor_first _ _).comp (isPureMor_first _ _)
  have hb : IsPureMor b := (isPureMor_first _ _).comp (isPureMor_second _ _)
  have hc : IsPureMor c := isPureMor_second _ _
  have e : pairArrows (pairArrows a b) c ≫
      (tensorLeft (productObj A B) f ≫ (tensorAssociator A B C').hom) =
      pairArrows (pairArrows a b) c ≫
      ((tensorAssociator A B C).hom ≫ tensorLeft A (tensorLeft B f)) := by
    simp only [← Category.assoc]
    rw [tensorLeft_pair (isPureMor_pairArrows ha hb) hc,
      assoc_pair_right ha hb _, assoc_pair_pure ha hb hc,
      tensorLeft_pair ha (isPureMor_pairArrows hb hc), tensorLeft_pair hb hc]
  have id : pairArrows (pairArrows a b) c = 𝟙 _ := triple_eta A B C
  simpa only [id, Category.id_comp] using e

end Silmaril.Thesis.LambdaIter.Syn.SynCat
