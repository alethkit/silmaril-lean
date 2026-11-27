module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Atoms.Branching.Direct.Renaming.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv HasType Pure)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural (Slot Assembly)
open scoped LetSeq.StraightLine.Structural Tagged Binary

variable {α Φ : Type} [TaggedSignature α Φ] {L : List (Ty α)}

/-! ## The normal form of a renamed tree

The normal form of a renamed spelled tree along a renaming is the normal
form of the tree along the composite. The proof follows the action, one
family at a time. -/

mutual

theorem Spelled.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {t : LetCase.LocallyNameless.Tm Empty Φ n} →
    (d : Spelled β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} → {k : Nat} → {δ : BoundCtx (Ty α) k} →
    (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, .ret exit payload, _, _, _, _, ρ, π => by
    simp only [Spelled.renamed, Spelled.normal]
    rw [assembly_rename_comp]
  | _, _, _, .ask f argument head, _, _, _, _, ρ, π => by
    have h := head.renamed_normal_proof ρ (.op f (argTerm (argument.rename ρ)))
      (congrArg (LetCase.LocallyNameless.Tm.op f) (argTerm_rename argument ρ)).symm π
    simp only [Spelled.renamed, Spelled.normal]
    rw [assembly_rename_comp, h]
  | _, _, _, .chain c, _, _, _, _, ρ, π => by
    have h := c.renamed_opened_proof ρ .nil rfl π
    simp only [Spelled.renamed, Spelled.normal]
    exact h

theorem SpelledHead.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {e t : LetCase.LocallyNameless.Tm Empty Φ n} → (d : SpelledHead tags e β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (e' : LetCase.LocallyNameless.Tm Empty Φ m) →
    (he : e' = e.rename ρ.toFun) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ e' he).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, _, .bind reply, _, _, _, _, ρ, _, _, π => by
    have h := reply.renamed_normal_proof ρ π
    simp only [SpelledHead.renamed, SpelledHead.normal]
    exact h
  | _, _, _, _, _, .destruct a b rest later, _, _, _, _, ρ, _, _, π => by
    have h := later.renamed_normal_proof (ρ.up (.base a)) (armRenaming π (tupleTy (a :: b :: rest)) (.base a))
    have e : (ρ.up (.base a)).comp (armRenaming π (tupleTy (a :: b :: rest)) (.base a)) =
        armRenaming (ρ.comp π) (tupleTy (a :: b :: rest)) (.base a) :=
      renaming_ext (Fin.cases rfl (fun _ => rfl))
    rw [e] at h
    simp only [SpelledHead.renamed, SpelledHead.normal]
    rw [h]
  | _, _, _, _, _, .branch atoms next rest left right, _, _, _, δ, ρ, _, _, π => by
    have hl := left.renamed_normal_proof ρ (π.comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))))
    have hr := right.renamed_normal_proof ρ (π.comp (BoundCtx.Renaming.succ δ (tagsTy (atoms :: next :: rest))))
    simp only [SpelledHead.renamed, SpelledHead.normal]
    rw [hl, hr]
    rfl

theorem SpelledTags.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {tags : List (List α)} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTags tags β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, .only atoms payload, _, _, _, _, ρ, π => by
    have h := payload.renamed_normal_proof ρ π
    simp only [SpelledTags.renamed, SpelledTags.normal]
    rw [h]
  | _, _, _, _, .split atoms next rest left right, _, _, _, _, ρ, π => by
    have hl := left.renamed_normal_proof (ρ.up (tagsTy (atoms :: next :: rest))) (π.up _)
    have hr := right.renamed_normal_proof (ρ.up (tagsTy (atoms :: next :: rest))) (π.up _)
    rw [renaming_up_comp] at hl hr
    simp only [SpelledTags.renamed, SpelledTags.normal]
    rw [hl, hr]

theorem SpelledTuple.renamed_normal_proof : {n : Nat} → {β : BoundCtx (Ty α) n} → {atoms : List α} →
    {t : LetCase.LocallyNameless.Tm Empty Φ (n + 1)} → (d : SpelledTuple atoms β L t) → {m : Nat} → {γ : BoundCtx (Ty α) m} →
    {k : Nat} → {δ : BoundCtx (Ty α) k} → (ρ : BoundCtx.Renaming β γ) → (π : BoundCtx.Renaming γ δ) →
    (d.renamed ρ).tree.normal π = d.normal (ρ.comp π)
  | _, _, _, _, .unit body, _, _, _, _, ρ, π => by
    have h := body.renamed_normal_proof (ρ.up (tupleTy ([] : List α))) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .atom a body, _, _, _, _, ρ, π => by
    have h := body.renamed_normal_proof (ρ.up (tupleTy [a])) (π.up _)
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .pair a b rest later, _, _, _, _, ρ, π => by
    have h := later.renamed_normal_proof ((ρ.up (tupleTy (a :: b :: rest))).up (.base a)) ((π.up _).up _)
    rw [renaming_up_comp, renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]
  | _, _, _, _, .hold atoms chain, _, _, _, _, ρ, π => by
    have h := chain.renamed_opened_proof (ρ.up (tupleTy atoms)) (.cons ⟨0, rfl⟩ .nil) rfl (π.up (tupleTy atoms))
    rw [renaming_up_comp] at h
    simp only [SpelledTuple.renamed, SpelledTuple.normal]
    rw [h]

theorem SpelledStack.renamed_opened_proof : {stack : List (List α)} → {m : Nat} → {Δ : BoundCtx (Ty α) m} →
    {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ m} → (d : SpelledStack stack Δ holds L t) → {k : Nat} →
    {Θ : BoundCtx (Ty α) k} → {j : Nat} → {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) →
    (holds' : Holds Θ stack) → (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π)
  | _, _, _, _, _, .done body, _, _, _, _, ρ, .nil, _, π => by
    have ih := body.renamed_normal_proof ρ π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    exact ih
  | _, _, _, .cons _ _, _, .unit next, _, _, _, _, ρ, .cons _ older', h, π =>
    next.renamed_opened_proof ρ older' (Holds.cons.inj h).2 π
  | _, _, _, .cons _ _, _, .atom next, _, _, _, _, ρ, .cons _ older', h, π =>
    next.renamed_opened_proof ρ older' (Holds.cons.inj h).2 π
  | (a :: b :: rest) :: stack, _, _, .cons _ older, _, .step next, _, Θ, _, Ξ, ρ, .cons _ older', h, π => by
    have ih := next.renamed_opened_proof ((ρ.up (.base a)).up (tupleTy (b :: rest)))
      (.cons ⟨0, rfl⟩ (older'.rename (pastPair Θ (.base a) (tupleTy (b :: rest)))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square older (pastPair Θ (.base a) (tupleTy (b :: rest)))
        (Holds.cons.inj h).2 (renaming_ext (fun _ => rfl))))
      ((π.up (.base a)).up (tupleTy (b :: rest)))
    rw [renaming_up_comp, renaming_up_comp] at ih
    exact congrArg (fun r : (u : LetCase.LocallyNameless.Tm Empty Φ _) × CaseTree .body _ L u =>
      CaseTree.renamed (pending := .body) r.2
        (upTele (swapStack stack Ξ [.base a, tupleTy (b :: rest)]) (pairsTele (b :: rest)))) ih
  | _, _, _, _, _, .ask g argument reply, _, _, _, _, ρ, holds', h, π => by
    have ih := reply.renamed_opened_proof ρ holds' h π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    rw [assembly_rename_comp, ih]
    rfl
  | _, _, _, holds, _, .pick sel next, _, _, _, _, ρ, holds', h, π => by
    have ih := next.renamed_opened_proof ρ (holds'.select sel)
      ((Holds.select_rename sel holds ρ).symm.trans (congrArg (Holds.select sel) h)) π
    simp only [SpelledStack.renamed, SpelledStack.opened]
    rw [ih]

theorem SpelledStackTags.renamed_opened_proof : {stack : List (List α)} → {tags : List (List α)} → {m : Nat} →
    {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1)} →
    (d : SpelledStackTags stack tags Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} → {j : Nat} →
    {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) →
    (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (d.renamed ρ holds' h).tree.opened π = d.opened (ρ.comp π)
  | _, _, _, _, holds, _, .bind atoms next, _, Θ, _, _, ρ, holds', h, π => by
    have ih := next.renamed_opened_proof (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) (π.up (tupleTy atoms))
    rw [renaming_up_comp] at ih
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ih]
  | _, _, _, _, holds, _, .split atoms next more left right, _, Θ, _, _, ρ, holds', h, π => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ihl, ihr]
  | _, tags, _, _, _, _, .later g argument arms, _, _, _, _, ρ, holds', h, π => by
    have ih := arms.renamed_opened_proof ρ holds' h π
      ((argument.rename (ρ.up (tagsTy tags))).rename (π.up (tagsTy tags)))
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ih, assembly_rename_comp, renaming_up_comp]
  | _, _, _, _, holds, _, .deferred atoms next more shape left right hl hr, _, Θ, _, _, ρ, holds', h, π => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledStackTags.renamed, SpelledStackTags.opened]
    rw [ihl, ihr]

theorem SpelledLaterTags.renamed_opened_proof : {stack : List (List α)} → {tags : List (List α)} → {g : Φ} →
    {m : Nat} → {Δ : BoundCtx (Ty α) m} → {holds : Holds Δ stack} → {t : LetCase.LocallyNameless.Tm Empty Φ (m + 1 + 1)} →
    (d : SpelledLaterTags stack tags g Δ holds L t) → {k : Nat} → {Θ : BoundCtx (Ty α) k} → {j : Nat} →
    {Ξ : BoundCtx (Ty α) j} → (ρ : BoundCtx.Renaming Δ Θ) → (holds' : Holds Θ stack) →
    (h : holds.rename ρ = holds') → (π : BoundCtx.Renaming Θ Ξ) →
    (arg : Assembly (Ξ.snoc (tagsTy tags)) (instrSrc g)) →
    (d.renamed ρ holds' h).tree.opened π arg = d.opened (ρ.comp π) arg
  | _, _, _, _, _, holds, _, .only atoms next, _, Θ, _, _, ρ, holds', h, π, arg => by
    have ih := next.renamed_opened_proof (ρ.up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (BoundCtx.Renaming.succ Θ (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds (BoundCtx.Renaming.succ Θ (tupleTy atoms)) h
        (renaming_ext (fun _ => rfl)))) (π.up (tupleTy atoms))
    rw [renaming_up_comp] at ih
    simp only [SpelledLaterTags.renamed, SpelledLaterTags.opened]
    rw [ih]
  | _, _, _, _, _, holds, _, .split atoms next more left right, _, Θ, _, Ξ, ρ, holds', h, π, arg => by
    have ihl := left.renamed_opened_proof ((ρ.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
      (.cons ⟨0, rfl⟩ (holds'.rename (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms))))
      (congrArg (Holds.cons ⟨0, rfl⟩) (holds_square holds
        (pastPair Θ (tagsTy (atoms :: next :: more)) (tupleTy atoms)) h (renaming_ext (fun _ => rfl))))
      ((π.up (tagsTy (atoms :: next :: more))).up (tupleTy atoms))
    have ihr := right.renamed_opened_proof (ρ.up (tagsTy (atoms :: next :: more)))
      (holds'.rename (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))))
      (holds_square holds (BoundCtx.Renaming.succ Θ (tagsTy (atoms :: next :: more))) h
        (renaming_ext (fun _ => rfl))) (π.up (tagsTy (atoms :: next :: more)))
      (arg.rename (BoundCtx.Renaming.succ (Ξ.snoc (tagsTy (atoms :: next :: more))) (tagsTy (next :: more))))
    rw [renaming_up_comp, renaming_up_comp] at ihl
    rw [renaming_up_comp] at ihr
    simp only [SpelledLaterTags.renamed, SpelledLaterTags.opened]
    rw [ihl, ihr]

end

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
