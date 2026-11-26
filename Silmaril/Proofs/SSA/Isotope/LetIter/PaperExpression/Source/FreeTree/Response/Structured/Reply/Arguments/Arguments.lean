module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Arguments.Defs
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Reply.Reflection.Thms
import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.CallByValue.Thms

public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.PureValues (ConstructorLeaf)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs

universe u r

variable {α Φ : Type u} [HasTy Φ (Ty α)] {ε : Type r} [HasEff Φ ε] [Preorder ε] [OrderBot ε]
  {Γ Δ : EffectCtx (Ty α) ε} {A B : Ty α} {e : ε} {a k : Expr Φ}

theorem leaf_subst (h : ConstructorLeaf a) {σ : Nat → Expr Φ}
    (hs : ∀ i, ConstructorLeaf (σ i)) : ConstructorLeaf (a.subst σ) := by
  induction h with
  | var i => exact hs i
  | unit => exact .unit
  | op _ ih => exact .op ih
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih

private theorem leaf_wk (h : ConstructorLeaf a) (ρ : Nat → Nat) : ConstructorLeaf (a.wk ρ) := by
  rw [Expr.wk_eq_subst]
  exact leaf_subst h (fun i => .var (ρ i))

theorem lift_leaf {σ : Nat → Expr Φ} (hs : ∀ i, ConstructorLeaf (σ i)) :
    ∀ i, ConstructorLeaf (Expr.liftSubst σ i)
  | 0 => .var 0
  | i + 1 => leaf_wk (hs i) Nat.succ

theorem lift_typed {σ : Nat → Expr Φ}
    (hs : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2)
    (slot : Ty α × ε) :
    ∀ i : Fin (slot :: Γ).length,
      Wf (slot :: Δ) (Expr.liftSubst σ i.val) ((slot :: Γ).get i).1 ((slot :: Γ).get i).2 := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .var 0 le_rfl
  · exact CallByValue.wf_wk0 (hs j) slot

theorem sequenced_wf (h : Sequenced e Γ A a) : Wf Γ a A e := by
  induction h with
  | leaf typed _ => exact typed.weakenEffect bot_le
  | call _ bound typed _ _ ih => exact .let₁ (.op bound (typed.weakenEffect bot_le)) ih

private theorem sequenced_subst (h : Sequenced e Γ A a) {σ : Nat → Expr Φ}
    (ht : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2)
    (hs : ∀ i, ConstructorLeaf (σ i)) : Sequenced e Δ A (a.subst σ) := by
  induction h generalizing Δ σ with
  | leaf typed leaf => exact .leaf (typed.subst_typed ht) (leaf_subst leaf hs)
  | call visible bound typed leaf _ ih =>
      exact .call visible bound (typed.subst_typed ht) (leaf_subst leaf hs)
        (ih (lift_typed ht _) (lift_leaf hs))

private theorem sequenced_wk0 (R : Ty α) (h : Sequenced e Γ A a) :
    Sequenced e ((R, ⊥) :: Γ) A a.wk0 := by
  unfold Expr.wk0
  rw [Expr.wk_eq_subst]
  exact sequenced_subst h (fun i => CallByValue.wf_wk0 (.var i le_rfl) (R, ⊥))
    (fun _ => .var _)

theorem wk1_subst_typed (R : Ty α) :
    ∀ i : Fin ((A, (⊥ : ε)) :: Γ).length,
      Wf ((A, ⊥) :: (R, ⊥) :: Γ) (Expr.var (Expr.liftWk Nat.succ i.val) : Expr Φ)
        (((A, (⊥ : ε)) :: Γ).get i).1 (((A, (⊥ : ε)) :: Γ).get i).2 := by
  intro i
  refine Fin.cases (.var 0 le_rfl) (fun j => ?_) i
  exact Wf.var (Γ := (A, ⊥) :: (R, ⊥) :: Γ) j.succ.succ le_rfl

private theorem sequenced_wk1 (R : Ty α) (h : Sequenced e ((A, ⊥) :: Γ) B k) :
    Sequenced e ((A, ⊥) :: (R, ⊥) :: Γ) B k.wk1 := by
  rw [Expr.wk1, Expr.wk_eq_subst]
  exact sequenced_subst h (wk1_subst_typed R) (fun _ => .var _)

theorem subst0_typed (h : Wf Γ a A (⊥ : ε)) :
    ∀ i : Fin ((A, (⊥ : ε)) :: Γ).length,
      Wf Γ (a.subst0 i.val) (((A, (⊥ : ε)) :: Γ).get i).1 (((A, (⊥ : ε)) :: Γ).get i).2 :=
  fun i => Fin.cases h (fun j => .var j le_rfl) i

theorem subst0_leaf (h : ConstructorLeaf a) :
    ∀ i, ConstructorLeaf (a.subst0 i)
  | 0 => h
  | i + 1 => .var i

private theorem sequenced_subst0 {v : Expr Φ} (ht : Wf Γ v A ⊥) (hl : ConstructorLeaf v)
    (h : Sequenced e ((A, ⊥) :: Γ) B k) : Sequenced e Γ B (k.subst v.subst0) :=
  sequenced_subst h (subst0_typed ht) (subst0_leaf hl)

theorem sequence (ha : Sequenced e Γ A a) (hk : Sequenced e ((A, ⊥) :: Γ) B k) :
    ∃ p, Eqv Γ B e (.let₁ a k) p ∧ Sequenced e Γ B p := by
  induction ha generalizing k with
  | leaf typed leaf =>
      exact ⟨_, .step (.let1_beta typed (sequenced_wf hk)), sequenced_subst0 typed leaf hk⟩
  | @call Δ X f arg bodyExpr visible bound typed leaf body ih =>
      have req := Wf.op bound (typed.weakenEffect bot_le)
      have weakened := sequenced_wk1 (instrTrg f) hk
      obtain ⟨p, hp, sp⟩ := ih weakened
      have eq := Eqv.step (.rewrite (.let₁ (.let₁ req (sequenced_wf body)) (sequenced_wf hk))
        (.let₁ req (.let₁ (sequenced_wf body) (sequenced_wf weakened))) (.let1_let1 _ _ _))
      exact ⟨_, eq.trans (.let1 (.refl req) hp), .call visible bound typed leaf sp⟩

theorem normalize (h : Raw e Γ A a) : ∃ p, Eqv Γ A e a p ∧ Sequenced e Γ A p := by
  induction h with
  | leaf typed leaf => exact ⟨_, .refl (typed.weakenEffect bot_le), .leaf typed leaf⟩
  | @call Δ f input visible bound _ ih =>
      obtain ⟨p, ep, sp⟩ := ih
      have arg : Wf ((instrSrc f, ⊥) :: Δ) (.var 0 : Expr Φ) (instrSrc f) ⊥ := .var 0 le_rfl
      have request := Wf.op (f := f) bound (arg.weakenEffect bot_le)
      have result : Sequenced e ((instrTrg f, ⊥) :: (instrSrc f, ⊥) :: Δ) (instrTrg f)
          (.var 0 : Expr Φ) := .leaf (.var 0 le_rfl) (.var 0)
      have next := Sequenced.call visible bound arg (.var 0) result
      have expose := Eqv.step (.rewrite (sequenced_wf next) request (.let1_eta _))
      obtain ⟨q, eq, sq⟩ := sequence sp next
      exact ⟨q, (Eqv.op bound ep).trans
        ((CallByValue.op_bind bound (sequenced_wf sp)).trans
          ((Eqv.let1 (.refl (sequenced_wf sp)) expose.symm).trans eq)), sq⟩
  | let1 _ _ ia ik =>
      obtain ⟨p, ep, sp⟩ := ia
      obtain ⟨q, eq, sq⟩ := ik
      obtain ⟨r, er, sr⟩ := sequence sp sq
      exact ⟨r, (Eqv.let1 ep eq).trans er, sr⟩
  | @pair Δ X Y left right _ _ il ir =>
      obtain ⟨p, ep, sp⟩ := il
      obtain ⟨q, eq, sq⟩ := ir
      have values : Sequenced e ((Y, ⊥) :: (X, ⊥) :: Δ) (.product X Y)
          (.pair (.var 1) (.var 0) : Expr Φ) :=
        .leaf (.pair (.var 1 le_rfl) (.var 0 le_rfl)) (.pair (.var 1) (.var 0))
      obtain ⟨inner, ei, si⟩ := sequence (sequenced_wk0 X sq) values
      obtain ⟨outer, eo, so⟩ := sequence sp si
      exact ⟨outer, (Eqv.pair ep eq).trans
        ((CallByValue.pair_bind (sequenced_wf sp) (sequenced_wf sq)).trans
          ((Eqv.let1 (.refl (sequenced_wf sp)) ei).trans eo)), so⟩

theorem shape_subst_typed {n : Nat} {sorts : Fin n → α} {R : Ty α}
    (shape : ReplyShape sorts R) :
    ∀ i : Fin ((R, (⊥ : ε)) :: Γ).length,
      Wf (ReplyShape.fieldCtx sorts Γ) (shape.sourceSubst Γ i.val : Expr Φ)
        (((R, (⊥ : ε)) :: Γ).get i).1 (((R, (⊥ : ε)) :: Γ).get i).2 :=
  fun i => shape.specialize_wf (Wf.var (Γ := (R, ⊥) :: Γ) i le_rfl)

omit [HasTy Φ (Ty α)] [HasEff Φ ε] in
theorem shape_subst_leaf {n : Nat} {sorts : Fin n → α} {R : Ty α}
    (shape : ReplyShape sorts R) :
    ∀ i, ConstructorLeaf (shape.sourceSubst Γ i : Expr Φ)
  | 0 => ReplyReflection.shape_constructor shape _
  | _ + 1 => .var _

theorem written_subst (h : Sequenced e Γ A a) {σ : Nat → Expr Φ}
    (ht : ∀ i : Fin Γ.length, Wf Δ (σ i.val) (Γ.get i).1 (Γ.get i).2)
    (hs : ∀ i, ConstructorLeaf (σ i)) : ReplyReflection.Written A e Δ (a.subst σ) := by
  induction h generalizing Δ σ with
  | leaf typed leaf => exact .of_leaf (typed.subst_typed ht) (leaf_subst leaf hs)
  | call visible bound typed leaf body ih =>
      refine .of_call visible bound (typed.subst_typed ht) (leaf_subst leaf hs)
        ((sequenced_wf body).subst_typed (lift_typed ht _)) ?_
      intro n sorts shape
      rw [ReplyShape.specialize, Expr.subst_comp]
      exact ih (fun i => (lift_typed ht _ i).subst_typed (shape_subst_typed shape))
        (fun i => leaf_subst (lift_leaf hs i) (shape_subst_leaf shape))

theorem written (h : Sequenced e Γ A a) : ReplyReflection.Written A e Γ a := by
  simpa only [Expr.subst_var] using written_subst h (σ := Expr.var) (fun i => .var i le_rfl) .var

theorem written_of_eqv (eq : Eqv Γ A e a k) (h : ReplyReflection.Written A e Γ k) :
    ReplyReflection.Written A e Γ a := by
  cases h with
  | leaf head typed leaf => exact .leaf (eq.trans head) typed leaf
  | call head visible bound typed leaf hk children =>
      exact .call (eq.trans head) visible bound typed leaf hk children

theorem raw_written (h : Raw e Γ A a) : ReplyReflection.Written A e Γ a := by
  obtain ⟨_, eq, sp⟩ := normalize h
  exact written_of_eqv eq (written sp)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.ReplyArguments.Proofs
