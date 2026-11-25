module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Closing.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Denotation
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Model.NamedValidity.Reopening

/-! # Soundness and reflection for addressable LetIter contexts -/

public section

open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation HasType AbortEquiv)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w r u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

namespace NamedContext

variable {ν : Type w} {τ : Type u} {Φ : Type v}

section Environment

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  [TypeFormers τ] (M : TypeModel τ V)

/-- Closing preserves the projection of each original bound index. -/
theorem closeEnv_bound (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    (closeEnvIso M Γ β).hom ≫
        boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := prepend (freeSlots Γ) β)
          (boundIndex Γ.length i) ≫
        eqToHom (congrArg M.obj (prepend_get_bound (freeSlots Γ) β i)) =
      boundVar M (Γ := Γ) (β := β) i :=
  DenotationProofs.closeEnv_bound M Γ β i

/-- Closing preserves free lookup at the slot selected by native lookup. -/
theorem closeEnv_free [DecidableEq ν] (Γ : Ctx ν τ) {n : Nat} (β : BoundCtx τ n)
    (x : ν) {A : τ} (h : Γ.lookup x = some A) (i : Fin Γ.length)
    (hi : lookupSlot x Γ = some i) (e : (freeSlots Γ).get i = A) :
    (closeEnvIso M Γ β).hom ≫
        boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := prepend (freeSlots Γ) β)
          (freeIndex i n) ≫
        eqToHom (congrArg M.obj ((prepend_get_free (freeSlots Γ) β i).trans e)) =
      freeLookup M (β := β) x h :=
  DenotationProofs.closeEnv_free M Γ β x h i hi e

end Environment

section Denotation

variable [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Closing preserves denotation under the canonical change of environment. -/
theorem denote_close
    {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M d = J.map ((closeEnvIso M Γ β).hom) ≫ denote J M (closeDerivation d) :=
  DenotationProofs.denote_close J M d

theorem denote_eq_iff_closed
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db ↔
      denote J M (closeDerivation da) = denote J M (closeDerivation db) :=
  DenotationProofs.denote_eq_iff_closed J M da db

/-- Coherence for all judgments with empty name type implies coherence for the given name type. -/
theorem typingCoherent_named_of_closing
    (closed : TypingCoherent (ν := Empty) J M Φ) :
    TypingCoherent (ν := ν) J M Φ :=
  DenotationProofs.typingCoherent_named_of_closing J M closed

end Denotation

section Reopening

variable [DecidableEq ν] {Γ : Ctx ν τ}

theorem visible_nil : AllSlotsVisible (Ctx.nil : Ctx ν τ) :=
  ReopeningProofs.visible_nil

theorem visible_snoc {x : ν} {A : τ} (visible : AllSlotsVisible Γ) (fresh : Γ.lookup x = none) :
    AllSlotsVisible (.snoc Γ (some x) A) :=
  ReopeningProofs.visible_snoc visible fresh

/-- Every slot in a newest-first indexed context is addressable after naming. -/
theorem nameIndexedSlots_visible (types : List τ) : AllSlotsVisible (nameIndexedSlots types) :=
  ReopeningProofs.nameIndexedSlots_visible types

variable [TypeFormers τ] [HasTy Φ τ] {ε : Type r} [HasEff Φ ε]

/-- Reopen a typed all-bound repaired equation using pure typed substitution. -/
theorem reopen_abortEquiv (pe : ε) (visible : AllSlotsVisible Γ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : HasType Φ Γ β a A) (db : HasType Φ Γ β b A)
    (h : AbortEquiv pe (Ctx.nil : Ctx Empty τ) (prepend (freeSlots Γ) β)
      (closeTm Γ a) (closeTm Γ b) A) :
    AbortEquiv pe Γ β a b A :=
  ReopeningProofs.reopen_abortEquiv pe visible da db h

end Reopening

end NamedContext

variable {ν : Type w} [DecidableEq ν]
  {τ Φ ε : Type} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
  {Γ : Ctx ν τ} (pe : ε)

/-- Abort equivalence is validity in the locally small model class whenever
native lookup reaches every free slot. The bound context is arbitrary. -/
theorem abortEquiv_iff_repairedNamedLocallySmallValidity (visible : NamedContext.AllSlotsVisible Γ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    AbortEquiv pe Γ β a b A ↔ RepairedNamedLocallySmallValidity pe da db :=
  NamedContext.DenotationProofs.abortEquiv_iff_repairedNamedLocallySmallValidity pe visible da db

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
