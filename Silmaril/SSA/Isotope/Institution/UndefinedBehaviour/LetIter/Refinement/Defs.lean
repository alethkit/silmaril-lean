module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LetIter.Thms

/-! # The LetIter specification interpreting literal UB as a unit-fed primitive -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB.LetIter

open CategoryTheory
open Silmaril.Logic.Institution
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Isotope.LetIter.LocallyNameless

universe u

variable {ν τ ε : Type u} [TypeFormers τ] [DecidableEq ν]

/-- The contextual signature of the ordinary, extended LetIter dialect. -/
abbrev dialectSignature (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ) : PSig.{u,u,u} :=
  @iterPSig τ _ ν _ (dialect P e).Instr (dialectTyping P) Γ

/-- The signature map carrying the original constructors into the extended dialect. -/
def relabel (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ) :
    iterPSig P.Instr Γ ⟶ dialectSignature P e Γ :=
  Institution.LetIter.sigHom Γ (includeDialect P e)

/-- The source specification uses the free extension of the original LetIter axioms. -/
def explicitSpec (P : InstrSig τ ε) (Γ : Ctx ν τ)
    (axioms : Set (Sentence (iterPSig P.Instr Γ))) : UB.Specification.{u,u} :=
  Specification.free ⟨iterPSig P.Instr Γ, axioms⟩

/-- Full native syntax, with the inherited sentences and an inequation from every
typed native term to the literal-unit UB at its sort. -/
def interpretedSpec (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ)
    (axioms : Set (Sentence (iterPSig P.Instr Γ))) : UB.Specification.{u,u} where
  sig := dialectSignature P e Γ
  axioms := Sentence.map (relabel P e Γ) '' axioms ∪
    {s | ∃ (i : TypingIndex τ) (t : Native P e Γ i), s = [⟨i, t, nativeUB P e Γ i⟩]}

/-- The preorders use consequence in the ordered refinement institution. -/
def explicitOrder (P : InstrSig τ ε) (Γ : Ctx ν τ)
    (axioms : Set (Sentence (iterPSig P.Instr Γ))) :=
  preorderOf ((Spec.closure institution).obj (explicitSpec P Γ axioms))

def interpretedOrder (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ)
    (axioms : Set (Sentence (iterPSig P.Instr Γ))) :=
  preorderOf ((Spec.closure institution).obj (interpretedSpec P e Γ axioms))

/-- The order on canonical native terms is inherited from the full native presentation. -/
@[instance_reducible] def canonicalPreorder (P : InstrSig τ ε) (e : ε) (Γ : Ctx ν τ)
    (axioms : Set (Sentence (iterPSig P.Instr Γ))) (i : TypingIndex τ) :
    Preorder {t : Native P e Γ i // Canonical P e Γ t} :=
  @Preorder.lift _ _ ((interpretedOrder P e Γ axioms).preorder i) Subtype.val

/-- Primitive rules for the full native refinement calculus. Inherited rules are
relabelled, and a typed term can refine the literal-unit UB at its sort. -/
def nativeRules (P : InstrSig τ ε) (e : ε)
    (R : TypedRelation ν P.Instr τ) : TypedRelation ν (dialect P e).Instr τ :=
  fun {_} β a b A =>
    (∃ x y, R β x y A ∧ a = x.mapInstr Sum.inl ∧ b = y.mapInstr Sum.inl) ∨
      b = .op (.inr A) .unit

/-- Actual native refinement includes the native equation schemes over the whole
extended dialect, in addition to the explicitly given primitive rules. -/
def nativeRefines (P : InstrSig τ ε) (e pureEff : ε) (Γ : Ctx ν τ)
    (R : TypedRelation ν P.Instr τ) {i : TypingIndex τ}
    (a b : Native P e Γ i) : Prop :=
  letI := dialectTyping P
  letI := (dialect P e).hasEff
  Silmaril.Isotope.LetIter.LocallyNameless.Refinement pureEff Γ (nativeRules P e R)
    i.bound a.1 b.1 i.result

end Silmaril.Isotope.Institution.Refinement.UB.LetIter
