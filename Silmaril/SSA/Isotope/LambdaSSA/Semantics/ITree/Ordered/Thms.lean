module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Comparison

/-! # Ordered satisfaction and reduct for typed packed programs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

open CategoryTheory
open scoped Silmaril.Elgot.ITree.WeakKleisli
open Silmaril.Elgot.ITree (TraceLE)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (denoteArrow)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Morphism (SignatureMap)
open Silmaril.Isotope.Semantics (encodeValue)

universe u v w

variable {κ : Type (u + 1)} [AtomValues κ] {Events : Type u → Type u}
  {Φ : Type v} {Ψ : Type w} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  [HasTy Ψ (Ty κ)] [HasEff Ψ Bool] {A B : Ty κ}

attribute [local instance] typeModel categoricalInstructions

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V
local notation "K" => typeJ (m := ModelTree Events)
local notation "T" => Categorical.ofMonadicTypeModel (τ := Ty κ)

/-- The typed order is exactly the erased trace comparison at encoded inputs.
The output encoding is injective and preserves the event family. -/
theorem denote_le_iff (M : Model (κ := κ) Events Φ) (N : Model (κ := κ) Events Ψ)
    (p : Program Φ A B) (q : Program Ψ A B) (env : Env (Sigma V)) :
    p.denote M ≤ q.denote N ↔ ∀ x : Interp A,
      TraceLE.{u, u+1} (region M.raw (extend env (encodeValue V A x)) p.code)
        (region N.raw (extend env (encodeValue V A x)) q.code) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.denote_le_iff M N p q env

/-- The packed program uses the denotation of the actual guarded packed arrow. -/
theorem denote_ofCFG (M : Model (κ := κ) Events Φ)
    {blocks exits : Nat} {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ}
    {g : FiniteCFG Φ blocks exits 0} (hg : g.HasType .nil R D) :
    (Program.ofCFG hg).denote M =
      (let _ := M.instructions; denoteArrow K T (FiniteCFG.packedExecution hg)) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.denote_ofCFG M hg

/-- At a common typed exit interface, satisfaction compares the literal
packed execution trees. The internal block interfaces may differ. -/
theorem satisfies_ofCFG_iff (M : Model (κ := κ) Events Φ)
    {blocks blocks' exits : Nat} {R : Fin blocks → Ty κ} {R' : Fin blocks' → Ty κ}
    {D : Fin exits → Ty κ} {g : FiniteCFG Φ blocks exits 0} {h : FiniteCFG Φ blocks' exits 0}
    (hg : g.HasType .nil R D) (hh : h.HasType .nil R' D) (env : Env (Sigma V)) :
    M.Satisfies (Program.ofCFG hg) (Program.ofCFG hh) ↔
      TraceLE.{u, u+1} (region M.raw env (FiniteCFG.packedExecutionRegion hg))
        (region M.raw env (FiniteCFG.packedExecutionRegion hh)) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.satisfies_ofCFG_iff M hg hh env

theorem Model.reduct_compatible (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (bottom : g.eff ⊥ = ⊥) :
    Compatible (κ' := κ) ⟨(M.reductInstructions g types bottom).denote⟩
      (fun f => M.raw (g.instr f)) :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.reduct_compatible M g types bottom

/-- The reduct interprets each source primitive by its target image. Runtime
values and the indexed event family remain shared. -/
@[expose] def Model.reduct (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id) (bottom : g.eff ⊥ = ⊥) :
    Model (κ := κ) Events Φ where
  instructions := M.reductInstructions g types bottom
  raw := fun f => M.raw (g.instr f)
  compatible := M.reduct_compatible g types bottom

/-- Relabelling a typed singleton program and evaluating in the target is
equal to evaluating the original program in the reduct. -/
theorem denote_reduct (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (bottom : g.eff ⊥ = ⊥) (p : Program Φ A B) :
    p.denote (M.reduct g types bottom) = (p.map g types).denote M :=
  Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.denote_reduct M g types p _ rfl

/-- Directed satisfaction is invariant under type-identity primitive
relabelling with a bottom-preserving effect component. -/
theorem satisfies_map_iff (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (bottom : g.eff ⊥ = ⊥) (p q : Program Φ A B) :
    M.Satisfies (p.map g types) (q.map g types) ↔ (M.reduct g types bottom).Satisfies p q := by
  simp only [Model.Satisfies, denote_reduct M g types bottom]

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
