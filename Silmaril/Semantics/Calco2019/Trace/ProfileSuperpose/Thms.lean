module

public import Silmaril.Semantics.Calco2019.Trace.ProfileSuperpose.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.ProfileSuperpose

/-! # Guarded superposition with separate marked interfaces -/

public section

universe u v

namespace Silmaril.Calco2019.Guardedness

open CategoryTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A B C D U A' B' C' D' : K}
  {f : P.sum (P.sum A U) B ⟶ P.sum C (P.sum D U)}
  {g : P.sum A' B' ⟶ P.sum C' D'}

theorem traceSuperpose_guard (hf : G.TraceGuard f) (hg : G.guarded (P.inl ≫ g)) :
    G.TraceGuard (traceSuperpose f g) :=
  Proofs.Feedback.profile_superpose_guard hf hg

/-- Trace a body with an independent guarded map alongside it, with
both pairs of marked interfaces grouped together. -/
theorem guardedTrace_superpose (F : G.Conway) (hf : G.TraceGuard f) (hg : G.guarded (P.inl ≫ g)) :
    F.toFixpoints.guardedTrace (traceSuperpose_guard hf hg) =
      exchangeMiddle P ≫ P.map (F.toFixpoints.guardedTrace hf) g ≫ exchangeMiddle P :=
  Proofs.Feedback.profile_superpose F hf hg

end Silmaril.Calco2019.Guardedness
