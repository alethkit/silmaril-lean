module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged

variable {α Φ : Type} {L : List (Ty α)}

/-! ## Renaming of exits and payloads -/

section Terms

variable {n : Nat} {β : BoundCtx (Ty α) n}

/-- Renaming commutes with returning at an exit. -/
theorem exit_term_rename_proof {A : Ty α} (e : ExitAt L A) {m : Nat} (ξ : Fin n → Fin m)
    (t : LetCase.LocallyNameless.Tm Empty Φ n) : (e.term t).rename ξ = e.term (t.rename ξ) := by
  induction e with
  | here => rfl
  | there later ih => exact congrArg LetCase.LocallyNameless.Tm.inr ih

/-- Renaming commutes with assembling a payload. -/
theorem argTerm_rename_proof {A : Ty α} (p : Assembly β A) {m : Nat} {γ : BoundCtx (Ty α) m}
    (ρ : BoundCtx.Renaming β γ) :
    (argTerm (Φ := Φ) p).rename ρ.toFun = argTerm (p.rename ρ) := by
  induction p with
  | atom s => rfl
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ LetCase.LocallyNameless.Tm.pair iha ihb

end Terms

/-! ## Renamings -/

section Algebra

variable [TaggedSignature α Φ] {n m k : Nat} {β : BoundCtx (Ty α) n} {γ : BoundCtx (Ty α) m}
  {δ : BoundCtx (Ty α) k}

omit [TaggedSignature α Φ] in
/-- Two renamings with the same function are equal. -/
theorem renaming_ext_proof {ρ π : BoundCtx.Renaming β γ} (same : ∀ i, ρ.toFun i = π.toFun i) : ρ = π := by
  cases ρ
  cases π
  congr
  funext i
  exact same i

omit [TaggedSignature α Φ] in
/-- Lifting under a new slot commutes with composition. -/
theorem renaming_up_comp_proof (ρ : BoundCtx.Renaming β γ) (π : BoundCtx.Renaming γ δ) (X : Ty α) :
    (ρ.up X).comp (π.up X) = (ρ.comp π).up X :=
  renaming_ext_proof (Fin.cases rfl (fun _ => rfl))

omit [TaggedSignature α Φ] in
/-- Renaming an assembled payload twice is renaming along the composite. -/
theorem assembly_rename_comp_proof {A : Ty α} (p : Assembly β A) (ρ : BoundCtx.Renaming β γ)
    (π : BoundCtx.Renaming γ δ) : (p.rename ρ).rename π = p.rename (ρ.comp π) := by
  induction p with
  | atom s => rfl
  | unit => rfl
  | pair a b iha ihb => exact congrArg₂ Assembly.pair iha ihb

end Algebra

/-! ## The renaming action on case trees -/

variable [TaggedSignature α Φ]

theorem renamed_term_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    ∀ {m : Nat} {γ : BoundCtx (Ty α) m} (ρ : CaseTree.Along pending β γ),
      CaseTree.RenamedTerm pending β γ t ρ (tree.renamed ρ) := by
  induction tree with
  | ret exit payload =>
    intro m γ ρ
    exact ((exit_term_rename_proof exit ρ.toFun _).trans (congrArg exit.term (argTerm_rename_proof payload ρ))).symm
  | ask f argument reply ih =>
    intro m γ ρ
    exact congrArg₂ LetCase.LocallyNameless.Tm.let₁
      (congrArg (LetCase.LocallyNameless.Tm.op f) (argTerm_rename_proof argument ρ).symm) (ih ρ)
  | only atoms payload ih => exact fun ρ => ih ρ
  | split atoms next rest left right ihl ihr =>
    intro m γ ρ
    exact congrArg₂ (LetCase.LocallyNameless.Tm.case (.bv 0)) (ihl (ρ.up _)) (ihr (ρ.up _))
  | unit body ih => exact fun ρ => ih (ρ.up _)
  | atom a body ih => exact fun ρ => ih (ρ.up _)
  | pair a b rest later ih =>
    intro m γ ρ
    exact congrArg (LetCase.LocallyNameless.Tm.let₂ (.bv 0)) (ih ((ρ.up _).up _))

theorem renamed_comp_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.RenamedComp pending β tree := by
  induction tree with
  | ret exit payload =>
    intro m γ k δ ρ π
    simp only [CaseTree.renamed]
    rw [assembly_rename_comp_proof]
  | ask f argument reply ih =>
    intro m γ k δ ρ π
    have h := ih ρ π
    simp only [CaseTree.renamed]
    rw [assembly_rename_comp_proof, h]
  | only atoms payload ih =>
    intro m γ k δ ρ π
    have h := ih ρ π
    simp only [CaseTree.renamed]
    rw [h]
  | split atoms next rest left right ihl ihr =>
    intro m γ k δ ρ π
    have hl := ihl (ρ.up _) (π.up _)
    have hr := ihr (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at hl hr
    simp only [CaseTree.renamed]
    rw [hl, hr]
  | unit body ih =>
    intro m γ k δ ρ π
    have h := ih (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]
  | atom a body ih =>
    intro m γ k δ ρ π
    have h := ih (ρ.up _) (π.up _)
    rw [renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]
  | pair a b rest later ih =>
    intro m γ k δ ρ π
    have h := ih ((ρ.up _).up _) ((π.up _).up _)
    rw [renaming_up_comp_proof, renaming_up_comp_proof] at h
    simp only [CaseTree.renamed]
    rw [h]

/-! ## Renaming and binding under a pending tuple -/

/-- Binding a slot under a renamed pending tuple is binding it under the
tuple along the composite renaming. -/
theorem pushed_pre_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedPre pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro j Ξ' ρ m Ω X π wrap
    have h := (renamed_comp_proof body (ρ.up _) ((π.up _).comp (swapRenaming Ω X _)))
    have e : (ρ.up (tupleTy ([] : List α))).comp ((π.up _).comp (swapRenaming Ω X _)) =
        ((ρ.comp π).up _).comp (swapRenaming Ω X _) := renaming_ext_proof (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
  | atom a body ih =>
    intro j Ξ' ρ m Ω X π wrap
    have h := (renamed_comp_proof body (ρ.up _) ((π.up _).comp (swapRenaming Ω X _)))
    have e : (ρ.up (tupleTy [a])).comp ((π.up _).comp (swapRenaming Ω X _)) =
        ((ρ.comp π).up _).comp (swapRenaming Ω X _) := renaming_ext_proof (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
  | @pair _ Ξ L a b rest body later ih =>
    intro j Ξ' ρ m Ω X π wrap
    have h := ih ((ρ.up _).up _) (((π.up _).up _).comp (afterPairRenaming Ω X _ _))
      (fun ω => wrap (((BoundCtx.Renaming.succ Ω _).comp (BoundCtx.Renaming.succ _ _)).comp ω))
    have e : ((ρ.up (tupleTy (a :: b :: rest))).up (Ty.base a)).comp
        (((π.up _).up _).comp (afterPairRenaming Ω X _ _)) =
        (((ρ.comp π).up _).up _).comp (afterPairRenaming Ω X _ _) :=
      renaming_ext_proof (Fin.cases rfl (fun i => Fin.cases rfl (fun _ => rfl) i))
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]

/-- Renaming commutes with binding a slot under a pending tuple, when the
way to bind the slot commutes with renaming. -/
theorem pushed_post_proof {pending : Pending α} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : LetCase.LocallyNameless.Tm Empty Φ n} (tree : CaseTree pending β L t) :
    CaseTree.PushedPost pending β tree := by
  induction tree with
  | ret exit payload => trivial
  | ask f argument reply ih => trivial
  | only atoms payload ih => trivial
  | split atoms next rest left right ihl ihr => trivial
  | unit body ih =>
    intro m Ω X π wrap natural j Ω' ω
    let T : Ty α := tupleTy ([] : List α)
    have step := natural (BoundCtx.Renaming.succ Ω T) (body.renamed ((π.up T).comp (swapRenaming Ω X T))).2
      (ω.up T)
    have h := renamed_comp_proof body ((π.up T).comp (swapRenaming Ω X T)) ((ω.up T).up X)
    have e : ((π.up T).comp (swapRenaming Ω X T)).comp ((ω.up T).up X) =
        ((π.comp (ω.up X)).up T).comp (swapRenaming Ω' X T) := by
      apply renaming_ext_proof
      intro i
      refine Fin.cases rfl (fun i => ?_) i
      change ((ω.up T).up X).toFun ((swapRenaming Ω X T).toFun (π.toFun i).succ) =
        (swapRenaming Ω' X T).toFun ((ω.up X).toFun (π.toFun i)).succ
      generalize π.toFun i = l
      exact Fin.cases rfl (fun _ => rfl) l
    have e' : (BoundCtx.Renaming.succ Ω T).comp (ω.up T) = ω.comp (BoundCtx.Renaming.succ Ω' T) :=
      renaming_ext_proof (fun _ => rfl)
    rw [e] at h
    rw [h, e'] at step
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [step]
  | atom a body ih =>
    intro m Ω X π wrap natural j Ω' ω
    let T : Ty α := tupleTy [a]
    have step := natural (BoundCtx.Renaming.succ Ω T) (body.renamed ((π.up T).comp (swapRenaming Ω X T))).2
      (ω.up T)
    have h := renamed_comp_proof body ((π.up T).comp (swapRenaming Ω X T)) ((ω.up T).up X)
    have e : ((π.up T).comp (swapRenaming Ω X T)).comp ((ω.up T).up X) =
        ((π.comp (ω.up X)).up T).comp (swapRenaming Ω' X T) := by
      apply renaming_ext_proof
      intro i
      refine Fin.cases rfl (fun i => ?_) i
      change ((ω.up T).up X).toFun ((swapRenaming Ω X T).toFun (π.toFun i).succ) =
        (swapRenaming Ω' X T).toFun ((ω.up X).toFun (π.toFun i)).succ
      generalize π.toFun i = l
      exact Fin.cases rfl (fun _ => rfl) l
    have e' : (BoundCtx.Renaming.succ Ω T).comp (ω.up T) = ω.comp (BoundCtx.Renaming.succ Ω' T) :=
      renaming_ext_proof (fun _ => rfl)
    rw [e] at h
    rw [h, e'] at step
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [step]
  | @pair _ Ξ L a b rest body later ih =>
    intro m Ω X π wrap natural j Ω' ω
    let T : Ty α := tupleTy (a :: b :: rest)
    let two : BoundCtx.Renaming Ω ((Ω.snoc T).snoc (Ty.base a)) :=
      (BoundCtx.Renaming.succ Ω T).comp (BoundCtx.Renaming.succ _ (Ty.base a))
    have h := ih (((π.up T).up (Ty.base a)).comp (afterPairRenaming Ω X T (Ty.base a)))
      (fun ω' => wrap (two.comp ω')) (fun ω₁ _ r _ _ ω₂ => natural (two.comp ω₁) r ω₂)
      ((ω.up T).up (Ty.base a))
    have e : (((π.up T).up (Ty.base a)).comp (afterPairRenaming Ω X T (Ty.base a))).comp
        (((ω.up T).up (Ty.base a)).up X) =
        (((π.comp (ω.up X)).up T).up (Ty.base a)).comp (afterPairRenaming Ω' X T (Ty.base a)) := by
      apply renaming_ext_proof
      intro i
      refine Fin.cases rfl (fun i => ?_) i
      refine Fin.cases rfl (fun i => ?_) i
      change (((ω.up T).up (Ty.base a)).up X).toFun (afterPair (π.toFun i).succ.succ) =
        afterPair ((ω.up X).toFun (π.toFun i)).succ.succ
      generalize π.toFun i = l
      exact Fin.cases rfl (fun _ => rfl) l
    rw [e] at h
    simp only [CaseTree.renamed, CaseTree.pushed]
    rw [h]
    rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
