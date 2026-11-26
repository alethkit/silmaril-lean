module

public import Silmaril.Proofs.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Bind

/-! # Normal environments and operands for source requests -/

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
  {Γ Δ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
  {A : Ty α} {e : ε}

omit [HasEff Ψ ε] in
public theorem value_subst {n m : Nat} {ss : Fin n → α} {target : Fin m → α}
    (v : Value S ss A) (hv : v.Pure (ε := ε) S)
    (θ : Sequence.TreeSubst S ss target) (hθ : ∀ i, DeclaredPure (ε := ε) S (θ i))
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (hξ : ∀ i : Fin n, ξ i.val = treeSource S (θ i)) :
    ∃ w : Value S target A, w.Pure (ε := ε) S ∧ (valueSource S v).subst ξ = valueSource S w := by
  induction v with
  | tree t =>
    exact ⟨.tree (t.interpret S _ Tree.op θ), Sequence.tree_pure_subst S t hv θ hθ,
      (Mixed.tree_subst_source S t θ ξ hξ).symm⟩
  | unit => exact ⟨.unit, trivial, rfl⟩
  | pair p q ihp ihq =>
    obtain ⟨p', hp', hpe⟩ := ihp hv.1
    obtain ⟨q', hq', hqe⟩ := ihq hv.2
    exact ⟨.pair p' q', ⟨hp', hq'⟩, congrArg₂ Expr.pair hpe hqe⟩
  | inl p ih =>
    obtain ⟨p', hp', he⟩ := ih hv
    exact ⟨.inl p', hp', congrArg Expr.inl he⟩
  | inr q ih =>
    obtain ⟨q', hq', he⟩ := ih hv
    exact ⟨.inr q', hq', congrArg Expr.inr he⟩

@[expose] public def NormalEnv {n : Nat} (ss : Fin n → α) (Δ : EffectCtx (Ty α) ε)
    (σ : Nat → Expr (Φ ⊕ Ψ)) : Prop :=
  ∀ i : Fin Δ.length, ∃ v : Value S ss (Δ.get i).1,
    v.Pure (ε := ε) S ∧ σ i.val = valueSource S v

omit [HasEff Ψ ε] in
public theorem NormalEnv.cons {n : Nat} {ss : Fin n → α} {σ : Nat → Expr (Φ ⊕ Ψ)}
    (hσ : NormalEnv S ss Δ σ) (v : Value S ss A) (hv : v.Pure (ε := ε) S) :
    NormalEnv S ss ((A, ⊥) :: Δ) (Proofs.cons (valueSource S v) σ) := by
  intro i
  exact Fin.cases (motive := fun j => ∃ p : Value S ss (((A, (⊥ : ε)) :: Δ).get j).1,
    p.Pure (ε := ε) S ∧ Proofs.cons (valueSource S v) σ j.val = valueSource S p)
    ⟨v, hv, rfl⟩ (fun j => hσ j) i

omit [HasEff Ψ ε] in
public theorem NormalEnv.subst {n m : Nat} {ss : Fin n → α} {target : Fin m → α}
    {σ : Nat → Expr (Φ ⊕ Ψ)} (hσ : NormalEnv S ss Δ σ)
    (θ : Sequence.TreeSubst S ss target) (hθ : ∀ i, DeclaredPure (ε := ε) S (θ i))
    (ξ : Nat → Expr (Φ ⊕ Ψ)) (hξ : ∀ i : Fin n, ξ i.val = treeSource S (θ i)) :
    NormalEnv S target Δ (fun i => (σ i).subst ξ) := by
  intro i
  obtain ⟨v, hv, he⟩ := hσ i
  obtain ⟨w, hw, hwEq⟩ := value_subst S v hv θ hθ ξ hξ
  exact ⟨w, hw, (congrArg (Expr.subst ξ) he).trans hwEq⟩

public theorem NormalEnv.typed {σ : Nat → Expr (Φ ⊕ Ψ)} (hσ : NormalEnv S slots Δ σ)
    (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) :
    letI := endpoints S T
    letI : HasEff (Φ ⊕ Ψ) ε := effects
    ∀ i : Fin Δ.length, Wf Γ (σ i.val) (Δ.get i).1 (Δ.get i).2 := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  intro i
  obtain ⟨v, hv, he⟩ := hσ i
  exact he ▸ (value_wf S T hΓ hs v hv).weakenEffect bot_le

omit [HasEff Ψ ε] in
public theorem NormalEnv.identity (hs : ∀ i, (Γ.get i).1 = .base (slots i)) :
    NormalEnv (Ψ := Ψ) S slots Γ Expr.var := by
  intro i
  exact (hs i).symm ▸ (show ∃ v : Value S slots (.base (slots i)),
      v.Pure (ε := ε) S ∧ (Expr.var i.val : Expr (Φ ⊕ Ψ)) = valueSource S v from
    ⟨.tree (.var i), trivial, rfl⟩)

omit [HasEff Ψ ε] in
private theorem value_arguments {k : Nat} {as : Fin k → α}
    (v : Value S slots (input k as)) (hv : v.Pure (ε := ε) S) :
    ∃ xs : (i : Fin k) → Tree S slots (as i),
      (∀ i, DeclaredPure (ε := ε) S (xs i)) ∧
        valueSource (Ψ := Ψ) S v = sourceTuple k (fun i => treeSource S (xs i)) := by
  induction k with
  | zero =>
    cases v
    exact ⟨fun i => i.elim0, fun i => i.elim0, rfl⟩
  | succ k ih =>
    cases v with
    | pair v rest =>
      cases v with
      | tree t =>
        obtain ⟨xs, hp, he⟩ := ih rest hv.2
        let args := Fin.cases (motive := fun i => Tree S slots (as i)) t xs
        refine ⟨args, Fin.cases (motive := fun i => DeclaredPure (ε := ε) S (args i)) hv.1 hp, ?_⟩
        exact congrArg (Expr.pair (treeSource S t)) he

public theorem normal_atom (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (f : Φ)
    (hf : instrEff f ≤ e) (v : Value S slots (input (S.arity f) (S.arg f))) (hv : v.Pure (ε := ε) S) :
    Normalizes S T Γ slots (.base (S.out f)) e (.op (.inl f) (valueSource S v)) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  classical
  obtain ⟨args, hp, he⟩ := value_arguments (Ψ := Ψ) S v hv
  rw [he]
  by_cases h : IsPure (⊥ : ε) f
  · exact normal_value S T hΓ hs (.tree (.op f args)) ⟨h, hp⟩
  · have hw := atom_request_wf S T hΓ hs args hp hf
    exact ⟨.atom f args (.ret (.tree (.var 0))), ⟨hp, h, hf, trivial⟩,
      (Eqv.step (.rewrite (.let₁ hw (.var 0 bot_le)) hw (.let1_eta _))).symm⟩

public theorem normal_sum (hΓ : Γ.Pure) (hs : ∀ i, (Γ.get i).1 = .base (slots i)) (g : Ψ)
    (hg : instrEff g ≤ e) (v : Value S slots (input (T.arity g) (T.arg g))) (hv : v.Pure (ε := ε) S) :
    Normalizes S T Γ slots (SumCall.result T g) e (.op (.inr g) (valueSource S v)) := by
  let instr := endpoints S T
  let eff : HasEff (Φ ⊕ Ψ) ε := effects
  obtain ⟨args, hp, he⟩ := value_arguments (Ψ := Ψ) S v hv
  rw [he]
  have hw := sum_request_wf S T hΓ hs args hp hg
  exact ⟨.sum g args (.ret (.inl (.tree (.var 0)))) (.ret (.inr (.tree (.var 0)))),
    ⟨hp, hg, trivial, trivial⟩,
    (Eqv.step (.rewrite (.case hw (.inl (.var 0 bot_le)) (.inr (.var 0 bot_le))) hw (.case_eta _))).symm⟩

public theorem no_empty_code {n : Nat} {ss : Fin n → α} (p : Code S T .empty ss) : False := by
  induction p with
  | ret v => cases v
  | atom _ _ _ ih => exact ih
  | sum _ _ _ _ ih _ => exact ih

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Mixed.Written.Proofs
