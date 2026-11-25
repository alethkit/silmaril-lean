module

public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Defs
import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Thms

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open LocallyNameless LocallyNameless.Tm LocallyNameless.Syntax

variable {S : Sig.{u}}

private theorem packTermPure : {n : Nat} → (β : BoundCtx S.Ty n) →
    Pure S.pureEff (packTerm β)
  | _, .nil => .unit
  | _, .snoc β _ => .pair ((packTermPure β).rename Fin.succ) .bv

private theorem projectPure {m : Nat} {p : Tm Empty S.Instr m} (hp : Pure S.pureEff p) :
    {n : Nat} → (β : BoundCtx S.Ty n) → (i : Fin n) → Pure S.pureEff (project β p i)
  | _, .nil, i => Fin.elim0 i
  | _, .snoc β _, i => Fin.cases (.let₂ hp .bv) (projectPure (.let₂ hp .bv) β) i

private def packingSubst {n : Nat} (β : BoundCtx S.Ty n) :
    PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff)
      β (.snoc .nil (packType β)) (project β (.bv 0)) :=
  ⟨projectTyping β HasType.newest, projectPure .bv β⟩

private def unpackingSubst {n : Nat} (β : BoundCtx S.Ty n) :
    PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff)
      (.snoc .nil (packType β)) β (fun _ => packTerm β) :=
  ⟨fun i => Fin.cases (packTermTyping β) (fun j => j.elim0) i, fun _ => packTermPure β⟩

private theorem upSub_eqv {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ θ : Fin n → Tm Empty S.Instr m}
    (e : ∀ i, Eqv S.pureEff Ctx.nil γ (σ i) (θ i) (β.get i)) (A : S.Ty) :
    ∀ i, Eqv S.pureEff Ctx.nil (.snoc γ A) (upSub σ i) (upSub θ i) ((β.snoc A).get i) :=
  Fin.cases (.refl HasType.newest) (fun i => (e i).rename (TypedRenaming.succ γ A))

private theorem subst_eqv {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n}
    {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A)
    {m : Nat} {γ : BoundCtx S.Ty m} {σ θ : Fin n → Tm Empty S.Instr m}
    (e : ∀ i, Eqv S.pureEff Ctx.nil γ (σ i) (θ i) (β.get i)) :
    Eqv S.pureEff Ctx.nil γ (bsubst σ t) (bsubst θ t) A := by
  induction h generalizing m with
  | fv h => exact .refl (.fv h)
  | bv => exact e _
  | op _ ih => exact .op (ih e)
  | unit => exact .unit
  | let₁ _ _ ih₁ ih₂ => exact .let₁ (ih₁ e) (ih₂ (upSub_eqv e _))
  | pair _ _ ih₁ ih₂ => exact .pair (ih₁ e) (ih₂ e)
  | let₂ _ _ ih₁ ih₂ => exact .let₂ (ih₁ e) (ih₂ (upSub_eqv (upSub_eqv e _) _))
  | inl _ ih => exact .inl (ih e)
  | inr _ ih => exact .inr (ih e)
  | case _ _ _ ih₁ ih₂ ih₃ => exact .case (ih₁ e) (ih₂ (upSub_eqv e _)) (ih₃ (upSub_eqv e _))
  | abort _ ih => exact .abort (ih e)
  | iter _ _ ih₁ ih₂ => exact .iter (ih₁ e) (ih₂ (upSub_eqv e _))

private theorem project_congr {m : Nat} {γ : BoundCtx S.Ty m} {p q : Tm Empty S.Instr m} :
    {n : Nat} → (β : BoundCtx S.Ty n) → Eqv S.pureEff Ctx.nil γ p q (packType β) →
      (i : Fin n) → Eqv S.pureEff Ctx.nil γ (project β p i) (project β q i) (β.get i)
  | _, .nil, _, i => Fin.elim0 i
  | _, .snoc β _, e, i => Fin.cases
      (.let₂ e (.refl HasType.newest))
      (project_congr β (.let₂ e (.refl (.bv (ι := 1))))) i

private theorem project_rename {n m k : Nat} (β : BoundCtx S.Ty n)
    (ρ : Fin m → Fin k) (p : Tm Empty S.Instr m) (i : Fin n) :
    rename ρ (project β p i) = project β (rename ρ p) i := by
  induction β generalizing p with
  | nil => exact Fin.elim0 i
  | snoc β _ ih =>
      refine Fin.cases rfl (fun j => ?_) i
      exact ih (.let₂ p (.bv 1)) j

private theorem project_bsubst {n m k : Nat} (β : BoundCtx S.Ty n)
    (σ : Fin m → Tm Empty S.Instr k) (p : Tm Empty S.Instr m) (i : Fin n) :
    bsubst σ (project β p i) = project β (bsubst σ p) i := by
  induction β generalizing p with
  | nil => exact Fin.elim0 i
  | snoc β _ ih =>
      refine Fin.cases rfl (fun j => ?_) i
      exact ih (.let₂ p (.bv 1)) j

private theorem project_packTerm {n : Nat} (β : BoundCtx S.Ty n) (i : Fin n) :
    Eqv S.pureEff Ctx.nil β (project β (packTerm β) i) (.bv i) (β.get i) := by
  induction β with
  | nil => exact Fin.elim0 i
  | snoc β B ih =>
      refine Fin.cases (second_beta (packTermTyping β).lift HasType.newest
        ((packTermPure β).rename Fin.succ)) (fun j => ?_) i
      have head := first_beta (S := S) (packTermTyping β).lift
        (HasType.newest (A := B)) .bv
      refine (project_congr β head j).trans ?_
      rw [show project β (lift (packTerm β)) j = lift (project β (packTerm β) j) from
        (project_rename β Fin.succ (packTerm β) j).symm]
      exact (ih j).rename (TypedRenaming.succ β B)

theorem unpacked_packed_proof {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    Eqv S.pureEff Ctx.nil β (unpackedTerm β (packedTerm β t)) t A := by
  rw [unpackedTerm, packedTerm, Syntax.bsubst_comp]
  have e := subst_eqv h (γ := β) (θ := Tm.bv)
    (σ := fun i => bsubst (fun _ : Fin 1 => packTerm β) (project β (.bv 0) i)) (fun i => by
      rw [project_bsubst, bsubst_bv]
      exact project_packTerm β i)
  rwa [Syntax.bsubst_bv_eq_rename, Syntax.rename_id] at e

private theorem packTerm_project {n m : Nat} (β : BoundCtx S.Ty n)
    {γ : BoundCtx S.Ty m} {p : Tm Empty S.Instr m}
    (h : HasType S.Instr Ctx.nil γ p (packType β)) (hp : Pure S.pureEff p) :
    Eqv S.pureEff Ctx.nil γ (bsubst (project β p) (packTerm β)) p (packType β) := by
  induction β generalizing p with
  | nil =>
      have hlet := HasType.let₁ h (HasType.unit (Φ := S.Instr))
      exact (Eqv.ax (.structural (.letBeta hp)) hlet .unit).symm.trans
        (Eqv.ax (.structural (.unitEta p)) hlet h)
  | snoc β B ih =>
      simp only [packTerm, bsubst_pair, bsubst_bv, lift, bsubst_rename]
      exact (Eqv.pair (ih (.let₂ h HasType.previous) (.let₂ hp .bv))
        (.refl (.let₂ h HasType.newest))).trans (pair_projections_eta h hp)

theorem packed_unpacked_proof {n : Nat} (β : BoundCtx S.Ty n)
    {t : Tm Empty S.Instr 1} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil (.snoc .nil (packType β)) t A) :
    Eqv S.pureEff Ctx.nil (.snoc .nil (packType β))
      (packedTerm β (unpackedTerm β t)) t A := by
  rw [packedTerm, unpackedTerm, Syntax.bsubst_comp]
  have e := subst_eqv h (γ := .snoc .nil (packType β)) (θ := Tm.bv)
    (σ := fun _ => bsubst (project β (.bv 0)) (packTerm β))
    (Fin.cases (packTerm_project β HasType.newest .bv) (fun i => i.elim0))
  rwa [Syntax.bsubst_bv_eq_rename, Syntax.rename_id] at e

def packedHomEquiv_proof {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) :
    El S β A ≃ (of (packType β) ⟶ of A) where
  toFun := Quotient.map
    (fun a => ⟨packedTerm β a.1, a.2.map packedTyping⟩)
    (fun _ _ e => Eqv.bsubst (packingSubst β) e)
  invFun := Quotient.map
    (fun a => ⟨unpackedTerm β a.1, a.2.map (HasType.bsubst (unpackingSubst β).typed)⟩)
    (fun _ _ e => Eqv.bsubst (unpackingSubst β) e)
  left_inv q := by
    induction q using Syn.ind with
    | H t h => exact Quotient.sound (unpacked_packed_proof h)
  right_inv q := by
    induction q using Syn.ind with
    | H t h => exact Quotient.sound (packed_unpacked_proof β h)

theorem packedHomEquiv_mk_proof {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedHomEquiv_proof β A (mk h) = packedArrow h := by rfl

private theorem instantiate_underBinder_one {t a : Tm Empty S.Instr 1} :
    instantiate (underBinder t) a = bsubst (fun _ : Fin 1 => a) t := by
  rw [instantiate, underBinder, bsubst_rename]
  apply bsubst_congr
  exact Fin.cases rfl (fun i => i.elim0)

theorem packedArrow_bv_succ_proof {n : Nat} (β : BoundCtx S.Ty n) (A : S.Ty) (i : Fin n) :
    packedArrow (S := S) (HasType.bv (β := .snoc β A) (ι := i.succ)) =
      first (of (packType β)) (of A) ≫ packedArrow (HasType.bv (β := β) (ι := i)) := by
  let firstProjection := HasType.let₂
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .nil) (A := tensor (packType β) A)) (HasType.bv (ι := 1))
  let projection := projectTyping β (HasType.newest (Γ := Ctx.nil) (β := .nil)) i
  have beta := Eqv.ax (.structural (.letBeta (pureEff := S.pureEff) (.let₂ .bv .bv)))
    (.let₁ firstProjection projection.underBinder) (projection.underBinder.instantiate firstProjection)
  change Eqv S.pureEff Ctx.nil _ _ (instantiate (underBinder (project β (.bv 0) i))
    (.let₂ (.bv 0) (.bv 1))) _ at beta
  rw [instantiate_underBinder_one, project_bsubst, bsubst_bv] at beta
  exact Quotient.sound beta.symm

/-- Applying the packed body to the retained environment and the newest
variable computes the lifted packing substitution. -/
private theorem packed_body_on_pair {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {b : Tm Empty S.Instr (n + 1)} (hb : HasType S.Instr Ctx.nil (.snoc β A) b B) :
    Eqv S.pureEff Ctx.nil (.snoc (.snoc .nil (packType β)) A)
      (bsubst (fun _ : Fin 1 => .pair (.bv 1) (.bv 0)) (packedTerm (.snoc β A) b))
      (bsubst (upSub (project β (.bv 0))) b) B := by
  rw [packedTerm, bsubst_comp]
  apply subst_eqv hb
  intro i
  rw [project_bsubst, bsubst_bv]
  let old := HasType.previous (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := .nil) (A := packType β) (B := A)
  let new := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := .snoc .nil (packType β)) (A := A)
  refine Fin.cases (second_beta old new .bv) (fun j => ?_) i
  change Eqv S.pureEff Ctx.nil _
    (project β (.let₂ (.pair (.bv 1) (.bv 0)) (.bv 1)) j) (lift (project β (.bv 0) j)) _
  rw [lift, project_rename]
  exact project_congr β (first_beta old new .bv) j

theorem packedArrow_let1_proof {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil (.snoc β A) b B) :
    packedArrow (S := S) (.let₁ ha hb) =
      pairArrows (𝟙 (of (packType β))) (packedArrow ha) ≫ packedArrow hb := by
  let p := packedTyping ha
  let q := packedTyping hb
  let x := HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
    (β := .nil) (A := packType β)
  let pair := HasType.pair x.lift (HasType.newest (A := A))
  have step := Eqv.ax (pureEff := S.pureEff) (.sequencing (.bindLet _ _ _))
    (.let₁ (.let₁ p pair) q.underBinder)
    (.let₁ p (.let₁ pair q.underBinder.underBinder))
  have beta := Eqv.ax (pureEff := S.pureEff) (.structural (.letBeta (.pair .bv .bv)))
    (.let₁ pair q.underBinder.underBinder) (q.underBinder.underBinder.instantiate pair)
  have subst_pair :
      instantiate (underBinder (underBinder (packedTerm (.snoc β A) b))) (.pair (.bv (Fin.succ 0)) (.bv 0)) =
        bsubst (fun _ : Fin 1 => .pair (.bv (Fin.succ 0)) (.bv 0)) (packedTerm (.snoc β A) b) := by
    rw [instantiate, underBinder, underBinder, bsubst_rename, bsubst_rename]
    exact bsubst_congr (Fin.cases rfl (fun i => i.elim0)) _
  rw [subst_pair] at beta
  apply Quotient.sound
  exact ((Eqv.let₁ (pair_pure_left_eqv x p .bv) (.refl q.underBinder)).trans
    (step.trans (.let₁ (.refl p) (beta.trans (packed_body_on_pair hb))))).symm

theorem packedArrow_op_proof {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {f : S.Instr}
    (h : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    packedArrow (S := S) (HasType.op (f := f) h) =
      packedArrow h ≫ mk (S := S) (HasType.op (f := f) HasType.newest) := by
  let p := packedTyping (S := S) h
  let q := HasType.op (f := f) p
  let r := HasType.op (ν := Empty) (f := f)
    (HasType.newest (Γ := Ctx.nil) (β := .snoc .nil (packType β)))
  apply Quotient.sound
  change Eqv S.pureEff Ctx.nil _ (.op f (packedTerm β a))
    (.let₁ (packedTerm β a) (.op f (.bv 0))) (instrTrg f)
  have eta := Eqv.ax (.structural (.letEta (pureEff := S.pureEff) _)) (.let₁ q .newest) q
  have seq := Eqv.ax (.sequencing (.bindOp (pureEff := S.pureEff) _ (.bv 0)))
    (.let₁ q .newest) (.let₁ p (.let₁ r .newest))
  exact eta.symm.trans (seq.trans (.let₁ (.refl p)
    (.ax (.structural (.letEta _)) (.let₁ r .newest) r)))

theorem packedArrow_inl_proof {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β a A) :
    packedArrow (S := S) (HasType.inl (B := B) h) =
      packedArrow h ≫ injl (of A) (of B) := by
  let argument := packedTyping (S := S) h
  let injection := HasType.inl (B := B) argument
  let left := HasType.inl (B := B)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil (packType β)) (A := A))
  let right := HasType.inr (A := A)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil (packType β)) (A := B))
  let split := HasType.case injection left right
  apply Quotient.sound
  exact (Eqv.ax (.structural (.caseEta (pureEff := S.pureEff) _)) split injection).symm.trans
    (Eqv.ax (.structural (.caseBetaL _ _ _)) split (.let₁ argument left))

theorem packedArrow_inr_proof {n : Nat} {β : BoundCtx S.Ty n} {A B : S.Ty}
    {a : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β a B) :
    packedArrow (S := S) (HasType.inr (A := A) h) =
      packedArrow h ≫ injr (of A) (of B) := by
  let argument := packedTyping (S := S) h
  let injection := HasType.inr (A := A) argument
  let left := HasType.inl (B := B)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil (packType β)) (A := A))
  let right := HasType.inr (A := A)
    (HasType.newest (Φ := S.Instr) (Γ := (Ctx.nil : Ctx Empty S.Ty))
      (β := .snoc .nil (packType β)) (A := B))
  let split := HasType.case injection left right
  apply Quotient.sound
  exact (Eqv.ax (.structural (.caseEta (pureEff := S.pureEff) _)) split injection).symm.trans
    (Eqv.ax (.structural (.caseBetaR _ _ _)) split (.let₁ argument right))

theorem packedSubst_comp_proof {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ)
    {t : Tm Empty S.Instr n} {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    packedSubst s ≫ packedArrow h = packedArrow (h.bsubst s.typed) := by
  let p := packedTerm γ (bsubst σ (packTerm β))
  let hp := packedTyping ((packTermTyping β).bsubst s.typed)
  have pp : Pure S.pureEff p := ((packTermPure β).bsubst s.pure).bsubst (packingSubst γ).pure
  have ht := (packedTyping h).underBinder (X := packType γ)
  apply Quotient.sound
  refine (Eqv.ax (.structural (.letBeta pp)) (.let₁ hp ht) (ht.instantiate hp)).trans ?_
  rw [instantiate_underBinder_one]
  change Eqv S.pureEff Ctx.nil (.snoc .nil (packType γ))
    (bsubst (fun _ : Fin 1 => p) (bsubst (project β (.bv 0)) t))
    (bsubst (project γ (.bv 0)) (bsubst σ t)) A
  rw [bsubst_comp, bsubst_comp]
  apply subst_eqv h
  intro i
  rw [project_bsubst, bsubst_bv]
  have e := ((project_packTerm β i).bsubst s).bsubst (packingSubst γ)
  rw [project_bsubst, project_bsubst, bsubst_bv] at e
  exact e

theorem packedSubst_isPureMor_proof {n m : Nat} {β : BoundCtx S.Ty n} {γ : BoundCtx S.Ty m}
    {σ : Fin n → Tm Empty S.Instr m}
    (s : PureTypedSubst (Γ := Ctx.nil) (pureEff := S.pureEff) β γ σ) :
    IsPureMor (packedSubst s) :=
  ⟨_, packedTyping ((packTermTyping β).bsubst s.typed),
    ((packTermPure β).bsubst s.pure).bsubst (packingSubst γ).pure, rfl⟩

theorem packedTerm_pure_proof {n : Nat} (β : BoundCtx S.Ty n) {t : Tm Empty S.Instr n}
    (hp : Pure S.pureEff t) : Pure S.pureEff (packedTerm β t) :=
  hp.bsubst (packingSubst β).pure

theorem packedArrow_isPureMor_proof {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty}
    {t : Tm Empty S.Instr n} (h : HasType S.Instr Ctx.nil β t A) (hp : Pure S.pureEff t) :
    IsPureMor (packedArrow h) :=
  ⟨_, packedTyping h, packedTerm_pure_proof β hp, rfl⟩

end Silmaril.Thesis.LambdaIter.Syn.SynCat
