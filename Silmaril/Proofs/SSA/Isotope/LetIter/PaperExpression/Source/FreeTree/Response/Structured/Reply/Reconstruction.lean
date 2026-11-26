module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reconstruction.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.ConstructorCover.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Equations.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Substitution.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ContextReflection.UnitSlot.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.ProductSplit.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.SumSplit.Thms

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm AbortEquiv HasTypeEffect)
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.ContextReflection

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs

universe u v w

variable {α : Type u} {Φ : Type v} {ε : Type w}

section Specialize

variable [Bot ε] {n : Nat} {sorts : Fin n → α} {R A : Ty α} {Γ : EffectCtx (Ty α) ε}
  (shape : ReplyShape sorts R)

public theorem get_fieldIndex (i : Fin n) : (fieldCtx sorts Γ).get (fieldIndex sorts Γ i) =
    (.base (sorts i), (⊥ : ε)) := by
  rw [List.get_eq_getElem]
  simp only [fieldIndex, Fin.val_cast, Fin.val_castAdd]
  unfold fieldCtx
  rw [List.getElem_append_left (by simp)]
  simp

public theorem get_ambientIndex (i : Fin Γ.length) :
    (fieldCtx sorts Γ).get (ambientIndex sorts Γ i) = Γ.get i := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  simp only [ambientIndex, Fin.val_cast, Fin.val_natAdd]
  unfold fieldCtx
  rw [List.getElem_append_right (by simp)]
  simp

public theorem specialize_lowers {body : Expr Φ} {t : Tm Empty Φ (Γ.length + 1)}
    (ht : body.toLetIter (Γ.length + 1) = some t) :
    (shape.specialize Γ body).toLetIter (fieldCtx sorts Γ).length = some (t.bsubst (shape.nativeSubst Γ)) := by
  apply Expr.toLetIter_subst ht
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact shape.lowers _
  · have h : n + j.val < (fieldCtx sorts Γ).length := (ambientIndex sorts Γ j).isLt
    simp only [sourceSubst, nativeSubst, Fin.cases_succ, Fin.val_succ, Expr.toLetIter,
      ambientIndex, dite_eq_left h]
    rfl

end Specialize

section TypedSpecialization

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {n : Nat} {sorts : Fin n → α} {R A : Ty α} {Γ : EffectCtx (Ty α) ε}
  (shape : ReplyShape sorts R) {e : ε} {body : Expr Φ}

private theorem typed_sourceSubst (i : Fin (((R, (⊥ : ε)) :: Γ).length)) :
    Wf (fieldCtx sorts Γ) (shape.sourceSubst Γ i.val : Expr Φ)
      (((R, (⊥ : ε)) :: Γ).get i).1 (((R, (⊥ : ε)) :: Γ).get i).2 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact shape.wf (fieldIndex sorts Γ) (get_fieldIndex (sorts := sorts) (Γ := Γ))
  · have a := Wf.var (Φ := Φ) (ambientIndex sorts Γ j) le_rfl
    rw [get_ambientIndex] at a
    exact a

public theorem specialize_wf (h : Wf ((R, ⊥) :: Γ) body A e) :
    Wf (fieldCtx sorts Γ) (shape.specialize Γ body) A e :=
  h.subst_typed (typed_sourceSubst shape)

end TypedSpecialization

section Transport

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {n : Nat} {sorts : Fin n → α} {R A : Ty α} {Γ : EffectCtx (Ty α) ε}
  (shape : ReplyShape sorts R) {a b : Expr Φ}

public theorem native_specialize (pureCtx : Γ.Pure) {t s : Tm Empty Φ (Γ.length + 1)}
    (ht : a.toLetIter (Γ.length + 1) = some t) (hs : b.toLetIter (Γ.length + 1) = some s)
    (h : AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) (EffectCtx.toBoundCtx ((R, (⊥ : ε)) :: Γ)) t s A) :
    AbortEquiv (⊥ : ε) (Ctx.nil : Ctx Empty (Ty α)) (fieldCtx sorts Γ).toBoundCtx
      (t.bsubst (shape.nativeSubst Γ)) (s.bsubst (shape.nativeSubst Γ)) A := by
  have hp : EffectCtx.Pure ((R, (⊥ : ε)) :: Γ) := fun i => Fin.cases rfl (fun j => pureCtx j) i
  obtain ⟨t', s', ht', hs', h⟩ := Source.native_subst hp ht hs h (typed_sourceSubst shape)
  have eT := Option.some.inj (ht'.symm.trans (specialize_lowers shape ht))
  have eS := Option.some.inj (hs'.symm.trans (specialize_lowers shape hs))
  simpa only [eT, eS] using h

public theorem specialize_hasTypeEffect {e : ε} (ha : Wf ((R, ⊥) :: Γ) a A e)
    {t : Tm Empty Φ (Γ.length + 1)} (ht : a.toLetIter (Γ.length + 1) = some t) :
    HasTypeEffect (Ctx.nil : Ctx Empty (Ty α)) (fieldCtx sorts Γ).toBoundCtx
      (t.bsubst (shape.nativeSubst Γ)) A e := by
  obtain ⟨u, hu, htyping⟩ := (specialize_wf shape ha).toLetIter
  exact (Option.some.inj (hu.symm.trans (specialize_lowers shape ht))) ▸ htyping

end Transport

section Reconstruction

variable [HasTy Φ (Ty α)] [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ Δ : EffectCtx (Ty α) ε} {A : Ty α} {e : ε} {a b : Expr Φ}

private abbrev Atomic (Δ : EffectCtx (Ty α) ε) :=
  ∀ i : Fin Δ.length, ∃ x, (Δ.get i).1 = .base x

private abbrev TypedMap (Δ Γ : EffectCtx (Ty α) ε) (σ : Nat → Expr Φ) :=
  ∀ i : Fin Γ.length, Wf Δ (σ i) (Γ.get i).1 (Γ.get i).2

private def Tests (Γ : EffectCtx (Ty α) ε) (A : Ty α) (e : ε) (a b : Expr Φ) : Prop :=
  ∀ Δ : EffectCtx (Ty α) ε, Atomic Δ → Δ.Pure → ∀ σ : Nat → Expr Φ,
    TypedMap Δ Γ σ → (∀ i, ConstructorCover.Value (σ i)) →
      Eqv Δ A e (a.subst σ) (b.subst σ)

private theorem tests_subst {θ : Nat → Expr Φ} (ht : TypedMap Δ Γ θ)
    (hv : ∀ i, ConstructorCover.Value (θ i)) (h : Tests Γ A e a b) :
    Tests Δ A e (a.subst θ) (b.subst θ) := by
  intro Ξ atomic pureCtx σ hσ hvσ
  rw [Expr.subst_comp, Expr.subst_comp]
  exact h Ξ atomic pureCtx _ (fun i => (ht i).subst_typed hσ)
    (fun i => (hv i).subst hvσ)

private theorem eqv_of_tests (cover : ConstructorCover Γ) (pureCtx : Γ.Pure)
    (ha : Wf Γ a A e) (hb : Wf Γ b A e) (h : Tests Γ A e a b) :
    Eqv Γ A e a b := by
  induction cover generalizing a b with
  | atomic atoms =>
    have eq := h _ atoms pureCtx Expr.var (fun i => .var i le_rfl) ConstructorCover.Value.var
    simpa only [Expr.subst_var] using eq
  | empty i ty eff => exact eqv_of_empty_slot i ty eff ha hb
  | unit i ty eff next ih =>
    have ht : TypedMap _ _ (UnitSlot.unitSubst i : Nat → Expr Φ) :=
      fun j => UnitSlot.wf_specializeUnit i ty eff (.var j le_rfl)
    have hv (j : Nat) : ConstructorCover.Value (UnitSlot.unitSubst i j : Expr Φ) := by
      unfold UnitSlot.unitSubst
      split
      · exact .unit
      · exact .var _
    exact (UnitSlot.eqv_iff_specializeUnit i ty eff ha hb).mpr
      (ih (UnitSlot.eraseCtx_pure pureCtx i) (UnitSlot.wf_specializeUnit i ty eff ha)
        (UnitSlot.wf_specializeUnit i ty eff hb) (tests_subst ht hv h))
  | product i ty eff next ih =>
    have ht : TypedMap _ _ (ProductSplit.splitSubst i : Nat → Expr Φ) :=
      fun j => ProductSplit.wf_split i ty eff (.var j le_rfl)
    have hv (j : Nat) : ConstructorCover.Value (ProductSplit.splitSubst i j : Expr Φ) := by
      unfold ProductSplit.splitSubst
      split
      · exact .pair (.var _) (.var _)
      · exact .var _
    exact (ProductSplit.eqv_iff_split i ty eff ha hb).mpr
      (ih (ProductSplit.splitCtx_pure pureCtx i _ _) (ProductSplit.wf_split i ty eff ha)
        (ProductSplit.wf_split i ty eff hb) (tests_subst ht hv h))
  | sum i ty eff left right ihL ihR =>
    have typed (j : Fin _) := SumSplit.wf_specializations i ty eff (Wf.var (Φ := Φ) j le_rfl)
    have value {p : Expr Φ} (hp : ConstructorCover.Value p) (j : Nat) :
        ConstructorCover.Value (SumSplit.replaceVar i p j) := by
      unfold SumSplit.replaceVar
      split
      · exact hp
      · exact .var _
    obtain ⟨hal, har⟩ := SumSplit.wf_specializations i ty eff ha
    obtain ⟨hbl, hbr⟩ := SumSplit.wf_specializations i ty eff hb
    exact (SumSplit.eqv_iff_specializations i ty eff ha hb).mpr
      ⟨ihL (SumSplit.branchCtx_pure pureCtx i _) hal hbl
          (tests_subst (fun j => (typed j).1) (value (.inl (.var _))) h),
        ihR (SumSplit.branchCtx_pure pureCtx i _) har hbr
          (tests_subst (fun j => (typed j).2) (value (.inr (.var _))) h)⟩

private theorem exists_rendering (atomic : Atomic Δ) (pureCtx : Δ.Pure)
    (ha : ConstructorCover.Value a) (hw : Wf Δ a A (⊥ : ε)) :
    ∃ (n : Nat) (sorts : Fin n → α) (shape : ReplyShape sorts A) (place : Fin n → Fin Δ.length),
      (∀ i, Δ.get (place i) = (.base (sorts i), ⊥)) ∧ shape.source place = a := by
  induction ha generalizing A with
  | var j =>
    cases hw with
    | var i _ =>
      obtain ⟨x, hx⟩ := atomic i
      rw [hx]
      exact ⟨1, fun _ => x, .atom x, fun _ => i, fun _ => Prod.ext hx (pureCtx i), rfl⟩
  | unit =>
    cases hw
    exact ⟨0, Fin.elim0, .unit, Fin.elim0, fun i => i.elim0, rfl⟩
  | pair _ _ ihL ihR =>
    cases hw with
    | pair hl hr =>
      obtain ⟨n, ss, left, placeL, slotL, eqL⟩ := ihL hl
      obtain ⟨m, ts, right, placeR, slotR, eqR⟩ := ihR hr
      refine ⟨n + m, Fin.addCases ss ts, .pair left right, Fin.addCases placeL placeR, ?_, ?_⟩
      · intro i
        refine Fin.addCases (motive := fun i =>
          Δ.get (Fin.addCases placeL placeR i) = (.base (Fin.addCases ss ts i), ⊥)) ?_ ?_ i
        · intro j
          simpa only [Fin.addCases_left] using slotL j
        · intro j
          simpa only [Fin.addCases_right] using slotR j
      · simp only [ReplyShape.source, Fin.addCases_left, Fin.addCases_right, eqL, eqR]
  | inl _ ih =>
    cases hw with
    | inl inner =>
      obtain ⟨n, ss, shape, place, typed, eq⟩ := ih inner
      exact ⟨n, ss, .inl shape, place, typed, congrArg Expr.inl eq⟩
  | inr _ ih =>
    cases hw with
    | inr inner =>
      obtain ⟨n, ss, shape, place, typed, eq⟩ := ih inner
      exact ⟨n, ss, .inr shape, place, typed, congrArg Expr.inr eq⟩

omit [HasTy Φ (Ty α)] in
private theorem source_wk {n m l : Nat} {sorts : Fin n → α} {R : Ty α}
    (shape : ReplyShape sorts R) (p : Fin n → Fin m) (q : Fin n → Fin l) (ρ : Nat → Nat)
    (h : ∀ i, ρ (p i).val = (q i).val) :
    (shape.source p : Expr Φ).wk ρ = shape.source q := by
  induction shape with
  | atom => exact congrArg Expr.var (h 0)
  | unit => rfl
  | pair _ _ ihL ihR =>
    exact congrArg₂ Expr.pair (ihL _ _ (fun i => h _)) (ihR _ _ (fun i => h _))
  | inl _ ih => exact congrArg Expr.inl (ih _ _ h)
  | inr _ ih => exact congrArg Expr.inr (ih _ _ h)

private theorem constructor_var (pureCtx : Δ.Pure) {x : α} (ha : ConstructorCover.Value a)
    (hw : Wf Δ a A (⊥ : ε)) (ht : A = .base x) :
    ∃ j : Fin Δ.length, a = .var j ∧ Δ.get j = (.base x, ⊥) := by
  cases ha with
  | var _ =>
    cases hw with
    | var j _ => exact ⟨j, rfl, Prod.ext ht (pureCtx j)⟩
  | unit => cases hw; cases ht
  | pair => cases hw; cases ht
  | inl => cases hw; cases ht
  | inr => cases hw; cases ht

private theorem eqv_at_leaf {R : Ty α} (atomic : Atomic Γ) (pureCtx : Γ.Pure)
    (ha : Wf ((R, ⊥) :: Γ) a A e) (hb : Wf ((R, ⊥) :: Γ) b A e)
    (h : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R),
      Eqv (fieldCtx sorts Γ) A e (shape.specialize Γ a) (shape.specialize Γ b)) :
    Tests ((R, ⊥) :: Γ) A e a b := by
  intro Δ atoms pureΔ σ hσ values
  obtain ⟨n, sorts, shape, place, fieldTy, rendered⟩ := exists_rendering atoms pureΔ (values 0) (hσ 0)
  have retained (i : Fin Γ.length) :
      ∃ j : Fin Δ.length, σ i.succ = .var j ∧ Δ.get j = Γ.get i := by
    obtain ⟨x, htype⟩ := atomic i
    have typed := hσ i.succ
    change Wf Δ (σ i.succ) (Γ.get i).1 (Γ.get i).2 at typed
    rw [pureCtx i] at typed
    obtain ⟨j, term, hj⟩ := constructor_var pureΔ (values i.succ) typed htype
    exact ⟨j, term, hj.trans (Prod.ext htype (pureCtx i)).symm⟩
  classical
  choose keep eqKeep keepTy using retained
  let pos : Fin (fieldCtx sorts Γ).length → Fin Δ.length :=
    fun i => Fin.addCases place keep (i.cast (fieldCtx_length sorts Γ))
  have placePos (i : Fin n) : pos (fieldIndex sorts Γ i) = place i := by
    simp [pos, fieldIndex, Fin.addCases_left]
  have keepPos (i : Fin Γ.length) : pos (ambientIndex sorts Γ i) = keep i := by
    simp [pos, ambientIndex, Fin.addCases_right]
  let ρ : Nat → Nat := fun j => if hj : j < (fieldCtx sorts Γ).length then (pos ⟨j, hj⟩).val else 0
  have ρpos (i : Fin (fieldCtx sorts Γ).length) : ρ i = (pos i).val := by
    simp only [ρ, dite_eq_left i.isLt]
  have posTy (i : Fin (fieldCtx sorts Γ).length) :
      Δ.get (pos i) = (fieldCtx sorts Γ).get i := by
    refine (Fin.addCases (motive := fun j =>
      Δ.get (pos (j.cast (fieldCtx_length sorts Γ).symm)) =
        (fieldCtx sorts Γ).get (j.cast (fieldCtx_length sorts Γ).symm)) ?_ ?_
      (i.cast (fieldCtx_length sorts Γ)))
    · intro j
      change Δ.get (pos (fieldIndex sorts Γ j)) = _
      rw [placePos]
      exact (fieldTy j).trans (get_fieldIndex (sorts := sorts) (Γ := Γ) j).symm
    · intro j
      change Δ.get (pos (ambientIndex sorts Γ j)) = _
      rw [keepPos]
      exact (keepTy j).trans (get_ambientIndex (sorts := sorts) (Γ := Γ) j).symm
  have hρ (i : Fin (fieldCtx sorts Γ).length) :
      Wf Δ (.var (ρ i) : Expr Φ) ((fieldCtx sorts Γ).get i).1 ((fieldCtx sorts Γ).get i).2 := by
    rw [ρpos, ← posTy]
    exact .var (pos i) le_rfl
  have body := (h shape).wk_typed hρ
  simp only [specialize, Expr.wk_subst] at body
  have images (i : Fin (((R, (⊥ : ε)) :: Γ).length)) :
      (shape.sourceSubst Γ i : Expr Φ).wk ρ = σ i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (source_wk shape (fieldIndex sorts Γ) place ρ (fun j => by rw [ρpos, placePos])).trans rendered
    · change Expr.var (ρ (n + j.val)) = σ j.succ
      rw [eqKeep]
      exact congrArg Expr.var ((ρpos (ambientIndex sorts Γ j)).trans (congrArg Fin.val (keepPos j)))
  have adjust {k : Expr Φ} (hk : Wf ((R, ⊥) :: Γ) k A e) :
      Eqv Δ A e (k.subst (fun j => (shape.sourceSubst Γ j).wk ρ)) (k.subst σ) :=
    hk.subst_congr fun i => by
      rw [images i]
      exact .refl (hσ i)
  exact (adjust ha).symm.trans (body.trans (adjust hb))

public theorem eqv_iff_specializations {R : Ty α}
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x) (pureCtx : Γ.Pure)
    (ha : Wf ((R, ⊥) :: Γ) a A e) (hb : Wf ((R, ⊥) :: Γ) b A e) :
    Eqv ((R, ⊥) :: Γ) A e a b ↔
      ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R),
        Eqv (fieldCtx sorts Γ) A e (shape.specialize Γ a) (shape.specialize Γ b) := by
  constructor
  · intro related n sorts shape
    exact related.subst_typed (typed_sourceSubst shape)
  · intro h
    have pureReply : EffectCtx.Pure ((R, (⊥ : ε)) :: Γ) :=
      fun i => Fin.cases rfl (fun j => pureCtx j) i
    obtain ⟨cover⟩ := ConstructorCover.exists_cover pureReply
    exact eqv_of_tests cover pureReply ha hb (eqv_at_leaf atomic pureCtx ha hb h)

public theorem eqv_let_of_specializations {R : Ty α} {request : Expr Φ}
    (atomic : ∀ i : Fin Γ.length, ∃ x, (Γ.get i).1 = .base x) (pureCtx : Γ.Pure)
    (hrequest : Wf Γ request R e) (ha : Wf ((R, ⊥) :: Γ) a A e) (hb : Wf ((R, ⊥) :: Γ) b A e)
    (h : ∀ {n : Nat} {sorts : Fin n → α} (shape : ReplyShape sorts R),
      Eqv (fieldCtx sorts Γ) A e (shape.specialize Γ a) (shape.specialize Γ b)) :
    Eqv Γ A e (.let₁ request a) (.let₁ request b) :=
  .let1 (.refl hrequest) ((eqv_iff_specializations atomic pureCtx ha hb).mpr h)

end Reconstruction

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyShape.Proofs
