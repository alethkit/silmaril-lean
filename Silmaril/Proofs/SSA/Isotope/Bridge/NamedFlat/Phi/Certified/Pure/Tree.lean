module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Defs
import Silmaril.Semantics.ITree.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture

open Silmaril.Isotope Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
open LambdaSSA (FiniteCFG Flat)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive term region)
open LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)

universe u v w x
variable {F : Type v} {Base : Type u} {n : Nat} {β : BoundCtx (Ty Base) n}
  {Events : Type w → Type w} {α : Type x}

private theorem embedTerm_tree (instr : Primitive Events F α) (slots : Env α)
    {m : Nat} (a : Tm Empty F m) (env : Env α) :
    term (treePrimitives (β := β) instr slots) env (erase (embedTerm a)) = term instr env (erase a) := by
  induction a generalizing env with
  | fv name => exact name.elim
  | bv | unit => rfl
  | op f a ih => simp only [embedTerm, erase, term, ih, treePrimitives]
  | let₁ a b iha ihb => simp only [embedTerm, erase, term, iha, ihb]
  | pair a b iha ihb => simp only [embedTerm, erase, term, iha, ihb]
  | let₂ a b iha ihb =>
      simp only [embedTerm, erase, term, iha]
      congr 1
      funext value
      cases value <;> simp only [ihb]
  | inl a ih | inr a ih | abort a ih => simp only [embedTerm, erase, term, ih]
  | case a l r iha ihl ihr =>
      simp only [embedTerm, erase, term, iha]
      congr 1
      funext value
      cases value <;> simp only [ihl, ihr]

private theorem embedFlat_tree (instr : Primitive Events F α) (slots : Env α)
    {labels m : Nat} (r : Flat F labels m) (env : Env α) :
    region (treePrimitives (β := β) instr slots) env (embedFlat r).erase = region instr env r.erase := by
  induction r generalizing env with
  | br i a => simp only [embedFlat, Flat.erase, region, embedTerm_tree]
  | let₁ a b ih => simp only [embedFlat, Flat.erase, region, embedTerm_tree, ih]
  | let₂ a b ih =>
      simp only [embedFlat, Flat.erase, region, embedTerm_tree]
      congr 1
      funext value
      cases value <;> simp only [ih]
  | case a l r ihl ihr =>
      simp only [embedFlat, Flat.erase, region, embedTerm_tree]
      congr 1
      funext value
      cases value <;> simp only [ihl, ihr]

theorem embed_tree (instr : Primitive Events F α) (slots : Env α)
    {blocks exits m : Nat} (g : FiniteCFG F blocks exits m) (env : Env α) :
    region (treePrimitives (β := β) instr slots) env (embed g).erase = region instr env g.erase := by
  simp only [embed, FiniteCFG.erase, region, embedFlat_tree]

private theorem assemble_tree {G : Type v} (instr : Primitive Events G α) (ambient : Env α)
    {m : Nat} (reads : Fin m → Tm Empty G 0) (slots : Env α)
    (pureReads : ∀ i, term instr ambient (erase (reads i)) = pure (slots i.val)) :
    term instr ambient (erase (assemble m reads)) = pure (NamedFlat.Capture.packEnv m slots) := by
  induction m generalizing slots with
  | zero => rfl
  | succ m ih =>
      simp only [assemble, erase, term, NamedFlat.Capture.packEnv]
      rw [ih (reads ∘ Fin.succ) (slots ∘ Nat.succ) (fun i => pureReads i.succ), pure_bind,
        pureReads 0, pure_bind]
      rfl

theorem packetInput_tree (instr : Primitive Events F α) (slots ambient : Env α) :
    term (treePrimitives (β := β) instr slots) ambient (erase (packetInput F β)) =
      pure (NamedFlat.Capture.packEnv n slots) :=
  assemble_tree _ _ _ _ (fun i => by simp only [erase, term, pure_bind, treePrimitives])

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture
