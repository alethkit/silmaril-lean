module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
open LambdaSSA (Flat FiniteCFG Region)
open LetCase.LocallyNameless (Tm HasType)

universe u v
variable {F : Type v} {Base : Type u} {n : Nat} {β : BoundCtx (Ty Base) n}
  [HasTy F (Ty Base)]

private theorem embedTerm_typed {m : Nat} {Δ : BoundCtx (Ty Base) m} {a : Tm Empty F m}
    {A : Ty Base} (typed : HasType F .nil Δ a A) :
    HasType (Instruction F β) .nil Δ (embedTerm a) A := by
  induction typed with
  | fv => exact Empty.elim (by assumption)
  | bv => exact .bv
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

private theorem embedFlat_typed {m labels : Nat} {L : Fin labels → Ty Base} {Δ : BoundCtx (Ty Base) m}
    {r : Flat F labels m} (typed : Flat.HasType L Δ r) : Flat.HasType L Δ (embedFlat (β := β) r) := by
  induction typed with
  | br arg => exact .br (embedTerm_typed arg)
  | let₁ arg _ ih => exact .let₁ (embedTerm_typed arg) ih
  | let₂ arg _ ih => exact .let₂ (embedTerm_typed arg) ih
  | case discr _ _ left right => exact .case (embedTerm_typed discr) left right

theorem embed_typed {m blocks exits : Nat} {Δ : BoundCtx (Ty Base) m} {R : Fin blocks → Ty Base}
    {L : Fin exits → Ty Base} {g : FiniteCFG F blocks exits m} (typed : g.HasType Δ R L) :
    (embed (β := β) g).HasType Δ R L :=
  ⟨embedFlat_typed typed.entry, fun i => embedFlat_typed (typed.block i)⟩

private theorem assemble_typed {G : Type v} [HasTy G (Ty Base)]
    {m : Nat} (Δ : BoundCtx (Ty Base) m) (slots : Fin m → Tm Empty G 0)
    (types : ∀ i, HasType G .nil .nil (slots i) (Δ.get i)) :
    HasType G .nil .nil (assemble m slots) (Region.packedInputType Δ.toList) := by
  induction Δ with
  | nil => exact .unit
  | snoc Δ A ih =>
      exact .pair (ih (slots ∘ Fin.succ) (fun i => types i.succ)) (types 0)

theorem packetInput_typed :
    HasType (Instruction F β) .nil .nil (packetInput F β) (Region.packedInputType β.toList) :=
  assemble_typed β _ (fun _ => .op .unit)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
