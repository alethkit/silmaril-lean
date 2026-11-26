module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.ModelAudit.InvariantCarrier.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Thms
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum
import Mathlib.Logic.Function.Basic

/-! # Cardinality obstruction to representing a feedback invariant subtype -/

public section

open CategoryTheory
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot.ITree

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.ModelAudit.InvariantCarrier

attribute [local instance] typeModel categoricalInstructions

theorem returns_iff (x : Atom) : Returns x ↔ ¬ IsSingleton x := by
  constructor
  · intro run
    induction run with
    | done out =>
      intro mark
      simp [next, mark] at out
    | @recur x y out _ ih =>
      intro mark
      have same : x = y := Sum.inr.inj (by simpa only [next, ite_eq_left mark] using out)
      exact ih (same ▸ mark)
  · intro mark
    exact .done (by rw [next, ite_eq_right mark])

private def singletonPoint (n : Nat) : Invariant :=
  ⟨⟨{n}⟩, ⟨n, rfl⟩⟩

private theorem singletonPoint_injective : Function.Injective singletonPoint := by
  intro n m h
  exact Set.singleton_injective (congrArg (fun x : Invariant => x.val.down) h)

private noncomputable def index (x : Invariant) : Nat := x.property.choose

private theorem index_injective : Function.Injective index := by
  intro x y eq
  apply Subtype.ext
  apply ULift.down_injective
  exact x.property.choose_spec.trans
    ((congrArg (fun n : Nat => ({n} : Set Nat)) eq).trans y.property.choose_spec.symm)

private theorem finite_or_embeds_atom (t : Ty AtomSort) :
    Finite (Ty.denote carrier t) ∨ Nonempty (Atom ↪ Ty.denote carrier t) := by
  classical
  induction t with
  | base _ => exact .inr ⟨Function.Embedding.refl _⟩
  | unit => exact .inl (by exact inferInstanceAs (Finite PUnit))
  | empty => exact .inl (by exact inferInstanceAs (Finite PEmpty))
  | coprod a b ia ib =>
    change Finite (Ty.denote carrier a ⊕ Ty.denote carrier b) ∨
      Nonempty (Atom ↪ Ty.denote carrier a ⊕ Ty.denote carrier b)
    rcases ia with ha | ea
    · rcases ib with hb | eb
      · exact .inl inferInstance
      · exact .inr ⟨(Classical.choice eb).trans ⟨Sum.inr, Sum.inr_injective⟩⟩
    · exact .inr ⟨(Classical.choice ea).trans ⟨Sum.inl, Sum.inl_injective⟩⟩
  | product a b ia ib =>
    change Finite (Ty.denote carrier a × Ty.denote carrier b) ∨
      Nonempty (Atom ↪ Ty.denote carrier a × Ty.denote carrier b)
    by_cases ha : Nonempty (Ty.denote carrier a)
    · by_cases hb : Nonempty (Ty.denote carrier b)
      · rcases ia with fa | ea
        · rcases ib with fb | eb
          · exact .inl inferInstance
          · let a₀ := Classical.choice ha
            exact .inr ⟨(Classical.choice eb).trans ⟨fun b => (a₀,b), fun _ _ h => congrArg Prod.snd h⟩⟩
        · let b₀ := Classical.choice hb
          exact .inr ⟨(Classical.choice ea).trans ⟨fun a => (a,b₀), fun _ _ h => congrArg Prod.fst h⟩⟩
      · let _ : IsEmpty (Ty.denote carrier b) := not_nonempty_iff.mp hb
        exact .inl inferInstance
    · let _ : IsEmpty (Ty.denote carrier a) := not_nonempty_iff.mp ha
      exact .inl inferInstance

/-- The nonterminating states have no carrier among the existing syntax types. -/
theorem no_invariant_carrier (t : Ty AtomSort) :
    ¬ Nonempty (Ty.denote carrier t ≃ {x : Atom // ¬ Returns x}) := by
  rintro ⟨e⟩
  let q : {x : Atom // ¬ Returns x} ≃ Invariant := Equiv.subtypeEquivRight (fun x => by
    rw [returns_iff]
    exact not_not)
  let f := e.trans q
  rcases finite_or_embeds_atom t with h | emb
  · let _ : Finite (Ty.denote carrier t) := h
    have fInj := f.symm.injective.comp singletonPoint_injective
    let _ : Finite Nat := Finite.of_injective _ fInj
    exact Infinite.false (inferInstance : Infinite Nat)
  · exact Function.cantor_injective _
      (index_injective.comp (f.injective.comp ((Classical.choice emb).injective.comp ULift.up_injective)))

theorem no_exact_inclusion (t : Ty AtomSort) (f : Ty.denote carrier t → Atom)
    (injective : Function.Injective f)
    (image : ∀ x, (∃ a, f a = x) ↔ ¬ Returns x) : False := by
  let toInvariant := fun a => (⟨f a, (image (f a)).mp ⟨a, rfl⟩⟩ : {x : Atom // ¬ Returns x})
  have bijective : Function.Bijective toInvariant := by
    constructor
    · intro a b h
      exact injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨a, h⟩ := (image x.val).mpr x.property
      exact ⟨a, Subtype.ext h⟩
  exact no_invariant_carrier t ⟨Equiv.ofBijective toInvariant bijective⟩

private theorem compatible :
    Compatible ⟨fun f x => InstructionModel.denote (τ := Ty AtomSort) (ε := Bool) (m := TreeM) f x⟩ raw := by
  intro f x
  change raw f (encodeValue carrier state x) =
    (pure (next x) >>= fun y => pure (encodeValue carrier result y))
  rw [pure_bind]
  rfl

theorem quotient_observation_sound {Γ : VCtx (Ty AtomSort)} {L : LCtx (Ty AtomSort)} {r s : Region Op}
    (eq : Paper.WithCaseReturns.Eqv false Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion computation typeInterpretation hr = denoteRegion computation typeInterpretation hs := by
  have := regionTypingCoherent raw compatible
  exact Paper.WithCaseReturns.Eqv.sound false computation typeInterpretation (fun _ _ => ⟨rfl, rfl⟩) eq hr hs

set_option backward.isDefEq.respectTransparency false in
private theorem encoded_step (x : Atom) :
    ((show TreeM _ from (denoteSingletonRegion computation typeInterpretation body_typed.hasType).of x) >>=
      fun y => pure (0, encodeValue carrier result y)) =
      pure (0, encodeValue carrier result (next x)) := by
  refine (singletonDenote_tree raw compatible body_typed.hasType x (fun _ => .unit)).trans ?_
  simp [body, Silmaril.Isotope.LambdaSSA.Semantics.Interaction.region,
    Silmaril.Isotope.LambdaSSA.Semantics.Interaction.term,
    Silmaril.Isotope.LambdaSSA.Semantics.extend, raw, encodeValue]

set_option backward.isDefEq.respectTransparency false in
theorem step_observation (x : Atom) :
    (show TreeM (PUnit.{2} ⊕ Atom) from
      (denoteSingletonRegion computation typeInterpretation body_typed.hasType).of x) = pure (next x) := by
  let label (y : PUnit.{2} ⊕ Atom) : Transfer (Sigma carrier) := (0, encodeValue carrier result y)
  let unlabel := Function.invFun label
  have inverse : ∀ y, unlabel (label y) = y :=
    Function.leftInverse_invFun (fun _ _ h => Silmaril.Isotope.Semantics.encodeValue_injective carrier result
      (congrArg Prod.snd h))
  have encoded := encoded_step x
  change ((show TreeM (PUnit.{2} ⊕ Atom) from
    (denoteSingletonRegion computation typeInterpretation body_typed.hasType).of x) >>=
    fun y => pure (label y)) = pure (label (next x)) at encoded
  have decoded := congrArg (fun tree : TreeM (Transfer (Sigma carrier)) =>
    tree >>= fun y => pure (unlabel y)) encoded
  simpa only [bind_assoc, pure_bind, inverse, bind_pure] using decoded

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.InvariantCarrier
