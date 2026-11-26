module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Bind.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms

/-! # Distribute a typed continuation across a finite mixed tree -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Normalization (Value)
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.SumCall
  (SumSignature treeSource endpoints effects)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs

universe u r

variable {α Φ Ψ : Type u} (S : Signature α Φ) (T : SumSignature α Ψ)
  {ε : Type r} [HasEff Φ ε] [HasEff Ψ ε] [SemilatticeSup ε] [OrderBot ε]
  {Γ Δ : EffectCtx (Ty α) ε} {A B : Ty α} {e : ε}

@[expose] public def cons (v : Expr (Φ ⊕ Ψ)) (σ : Nat → Expr (Φ ⊕ Ψ)) : Nat → Expr (Φ ⊕ Ψ)
  | 0 => v
  | i + 1 => σ i

public theorem subst_wk0_cons (a v : Expr (Φ ⊕ Ψ)) (σ : Nat → Expr (Φ ⊕ Ψ)) :
    a.wk0.subst (cons v σ) = a.subst σ := by
  rw [Expr.wk0, Expr.subst_wk]
  rfl

public theorem subst_lift_cons (a v : Expr (Φ ⊕ Ψ)) (σ ξ : Nat → Expr (Φ ⊕ Ψ)) :
    (a.subst (Expr.liftSubst σ)).subst (cons v ξ) =
      a.subst (cons v (fun i => (σ i).subst ξ)) := by
  rw [Expr.subst_comp]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i => exact subst_wk0_cons _ _ _

public theorem typed_lift {ξ : Nat → Expr (Φ ⊕ Ψ)}
    (h : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
         ∀ i : Fin Δ.length, Wf Γ (ξ i.val) (Δ.get i).1 (Δ.get i).2) (slot : Ty α × ε) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ i : Fin (slot :: Δ).length, Wf (slot :: Γ) (Expr.liftSubst ξ i.val)
      ((slot :: Δ).get i).1 ((slot :: Δ).get i).2 := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  intro i
  exact Fin.cases (motive := fun i => Wf (slot :: Γ) (Expr.liftSubst ξ i.val)
    ((slot :: Δ).get i).1 ((slot :: Δ).get i).2) (.var 0 le_rfl)
    (fun j => CallByValue.wf_wk0 (h j) slot) i

public theorem wf_wk1 {b : Expr (Φ ⊕ Ψ)} (x : Ty α)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
          Wf ((A, ⊥) :: Γ) b B e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf ((A, ⊥) :: (x, ⊥) :: Γ) b.wk1 B e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  rw [Expr.wk1, Expr.wk_eq_subst]
  apply hb.subst_typed
  intro i
  refine Fin.cases (motive := fun i => Wf ((A, (⊥ : ε)) :: (x, ⊥) :: Γ)
    (Expr.var (Expr.liftWk Nat.succ i.val)) (((A, (⊥ : ε)) :: Γ).get i).1
      (((A, (⊥ : ε)) :: Γ).get i).2) (.var 0 le_rfl) ?_ i
  intro j
  exact Wf.var (Γ := (A, ⊥) :: (x, ⊥) :: Γ) j.succ.succ le_rfl

public theorem value_wf {slots : Fin Γ.length → α}
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    (v : Value S slots A) (hv : v.Pure (ε := ε) S) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ (valueSource (Ψ := Ψ) S v) A (⊥ : ε) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction v with
  | tree t => exact tree_wf S T hΓ hs t hv _
  | unit => exact .unit _ _
  | pair p q ihp ihq => exact .pair (ihp hv.1) (ihq hv.2)
  | inl p ih => exact .inl (ih hv)
  | inr q ih => exact .inr (ih hv)

private theorem code_wf_aux {n : Nat} {slots : Fin n → α} (p : Code S T A slots)
    (hp : p.WellTyped S T e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (slots (i.cast hlen))) → Wf Γ p.source A e := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p with
  | @ret n ss v =>
    intro Γ hlen hΓ hs
    subst n
    exact (value_wf S T hΓ hs v hp).weakenEffect bot_le
  | @atom n ss f args next ih =>
    intro Γ hlen hΓ hs
    subst n
    exact .let₁ (atom_request_wf S T hΓ hs args hp.1 hp.2.2.1)
      (ih hp.2.2.2 rfl (pure_extended hΓ _) (slots_extended hs))
  | @sum n ss g args left right ihl ihr =>
    intro Γ hlen hΓ hs
    subst n
    exact .case (sum_request_wf S T hΓ hs args hp.1 hp.2.1)
      (ihl hp.2.2.1 rfl (pure_extended hΓ _) (slots_extended hs))
      (ihr hp.2.2.2 rfl (pure_extended hΓ _) (slots_extended hs))

public theorem code_wf {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (p : Code S T A slots) (hp : p.WellTyped S T e) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    Wf Γ p.source A e :=
  code_wf_aux S T p hp rfl hΓ hs

@[expose] public def Normalizes (Γ : EffectCtx (Ty α) ε) (slots : Fin Γ.length → α)
    (A : Ty α) (e : ε) (p : Expr (Φ ⊕ Ψ)) : Prop :=
  letI := endpoints S T
  letI : HasEff (Φ ⊕ Ψ) ε := effects
  ∃ q : Code S T A slots, q.WellTyped S T e ∧ Eqv Γ A e p q.source

public theorem Normalizes.of_eqv {slots : Fin Γ.length → α} {a b : Expr (Φ ⊕ Ψ)}
    (h : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects; Eqv Γ A e a b)
    (hb : Normalizes S T Γ slots A e b) : Normalizes S T Γ slots A e a := by
  unfold Normalizes at hb ⊢
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨q, hq, he⟩ := hb
  exact ⟨q, hq, h.trans he⟩

public theorem normal_value {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (v : Value S slots A) (hv : v.Pure (ε := ε) S) :
    Normalizes S T Γ slots A e (valueSource S v) := by
  unfold Normalizes
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  exact ⟨.ret v, hv, .refl ((value_wf S T hΓ hs v hv).weakenEffect bot_le)⟩

/-- The continuation handles a pure result in every atomically substituted
environment. The request binders are precisely the uses of this generality. -/
@[expose] public def Continuation {n : Nat} (slots : Fin n → α)
    (A B : Ty α) (e : ε) (b : Expr (Φ ⊕ Ψ)) : Prop :=
  ∀ {Δ : EffectCtx (Ty α) ε} {target : Fin Δ.length → α}, Δ.Pure →
    (∀ i, (Δ.get i).1 = .base (target i)) →
    ∀ (θ : Sequence.TreeSubst S slots target), (∀ i, DeclaredPure (ε := ε) S (θ i)) →
    ∀ (ξ : Nat → Expr (Φ ⊕ Ψ)), (∀ i : Fin n, ξ i.val = treeSource S (θ i)) →
    ∀ (v : Value S target A), v.Pure (ε := ε) S →
      Normalizes S T Δ target B e (b.subst (cons (valueSource S v) ξ))

private theorem continuation_wk1 {n : Nat} {slots : Fin n → α}
    (b : Expr (Φ ⊕ Ψ)) (x : α) (h : Continuation S T slots A B e b) :
    Continuation S T (extendSorts x slots) A B e b.wk1 := by
  intro Δ target hΔ hs θ hθ ξ hξ v hv
  have hbody : b.wk1.subst (cons (valueSource S v) ξ) =
      b.subst (cons (valueSource S v) (ξ ∘ Nat.succ)) := by
    rw [Expr.wk1, Expr.subst_wk]
    congr 1
    funext i
    cases i <;> rfl
  rw [hbody]
  exact h hΔ hs (fun i => θ i.succ) (fun i => hθ i.succ) (ξ ∘ Nat.succ) (fun i => hξ i.succ) v hv

private theorem bind_aux {n : Nat} {ss : Fin n → α} (p : Code S T A ss)
    (hp : p.WellTyped S T e) {b : Expr (Φ ⊕ Ψ)} (hk : Continuation S T ss A B e b) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ {Γ : EffectCtx (Ty α) ε} (hlen : Γ.length = n), Γ.Pure →
      (∀ i : Fin Γ.length, (Γ.get i).1 = .base (ss (i.cast hlen))) →
        Wf ((A, ⊥) :: Γ) b B e →
        Normalizes S T Γ (fun i => ss (i.cast hlen)) B e (.let₁ p.source b) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  induction p generalizing b with
  | @ret n ss v =>
    intro Γ hlen hΓ hs hb
    subst n
    have he := Eqv.step (Step.let1_beta (value_wf S T hΓ hs v hp) hb)
    exact Normalizes.of_eqv S T he (hk hΓ hs Tree.var (fun _ => trivial) Expr.var (fun _ => rfl) v hp)
  | @atom n ss f args next ih =>
    intro Γ hlen hΓ hs hb
    subst n
    let x := S.out f
    have hx := pure_extended hΓ x
    have hsx := slots_extended (a := x) hs
    have hw := wf_wk1 S T (.base x) hb
    obtain ⟨q, hq, he⟩ := ih hp.2.2.2 (continuation_wk1 S T b x hk) rfl hx hsx hw
    have hf := atom_request_wf S T hΓ hs args hp.1 hp.2.2.1
    have hn := code_wf S T hx hsx next hp.2.2.2
    refine ⟨.atom f args q, ⟨hp.1, hp.2.1, hp.2.2.1, hq⟩, ?_⟩
    exact (Eqv.step (.rewrite (.let₁ (.let₁ hf hn) hb)
      (.let₁ hf (.let₁ hn hw)) (.let1_let1 _ _ _))).trans (.let1 (.refl hf) he)
  | @sum n ss g args left right ihl ihr =>
    intro Γ hlen hΓ hs hb
    subst n
    have hΓl := pure_extended hΓ (T.left g)
    have hΓr := pure_extended hΓ (T.right g)
    have hsl := slots_extended (a := T.left g) hs
    have hsr := slots_extended (a := T.right g) hs
    have hbl := wf_wk1 S T (.base (T.left g)) hb
    have hbr := wf_wk1 S T (.base (T.right g)) hb
    obtain ⟨ql, hql, hel⟩ := ihl hp.2.2.1 (continuation_wk1 S T b _ hk) rfl hΓl hsl hbl
    obtain ⟨qr, hqr, her⟩ := ihr hp.2.2.2 (continuation_wk1 S T b _ hk) rfl hΓr hsr hbr
    have hg := sum_request_wf S T hΓ hs args hp.1 hp.2.1
    have hl := code_wf S T hΓl hsl left hp.2.2.1
    have hr := code_wf S T hΓr hsr right hp.2.2.2
    refine ⟨.sum g args ql qr, ⟨hp.1, hp.2.1, hql, hqr⟩, ?_⟩
    exact (Eqv.step (.rewrite (.let₁ (.case hg hl hr) hb)
      (.case hg (.let₁ hl hbl) (.let₁ hr hbr)) (.let1_case _ _ _ _))).trans (.case (.refl hg) hel her)

public theorem bind {slots : Fin Γ.length → α} (hΓ : Γ.Pure)
    (hs : ∀ i, (Γ.get i).1 = .base (slots i))
    {a b : Expr (Φ ⊕ Ψ)} (ha : Normalizes S T Γ slots A e a)
    (hb : letI := endpoints S T; letI : HasEff (Φ ⊕ Ψ) ε := effects
          Wf ((A, ⊥) :: Γ) b B e) (hk : Continuation S T slots A B e b) :
    Normalizes S T Γ slots B e (.let₁ a b) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨p, hp, he⟩ := ha
  exact Normalizes.of_eqv S T (.let1 he (.refl hb)) (bind_aux S T p hp hk rfl hΓ hs hb)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs
