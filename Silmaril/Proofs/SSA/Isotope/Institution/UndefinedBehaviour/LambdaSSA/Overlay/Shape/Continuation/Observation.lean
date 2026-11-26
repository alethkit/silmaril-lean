module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape

universe u v w x

variable {Φ : Type u} {α : Type w} {σ : Type x}

/-- The transition relations shared by both sides of an operational comparison. -/
structure Ops (Φ : Type u) (α : Type w) (σ : Type x) where
  instr : Φ → Value α → σ → Value α → σ → Prop
  faults : Φ → Value α → σ → σ → Prop
  prim : Φ → Value α → σ → Prop

variable {O : Ops Φ α σ} {env env' env'' : Env α}

structure TermAt (O : Ops Φ α σ) (env : Env α) (a : Tm Φ) (env' : Env α) (b : Tm Φ) : Prop where
  eval : ∀ {s v t}, Semantics.Tm.Eval O.instr env a s v t ↔ Semantics.Tm.Eval O.instr env' b s v t
  fault : ∀ {s t}, Semantics.Tm.Fault O.instr O.faults env a s t ↔ Semantics.Tm.Fault O.instr O.faults env' b s t
  div : ∀ {s}, Semantics.Tm.ExternalDiverges O.instr O.prim env a s ↔
    Semantics.Tm.ExternalDiverges O.instr O.prim env' b s

structure RegionAt (O : Ops Φ α σ) (env : Env α) (r : Region Φ) (env' : Env α) (t : Region Φ) : Prop where
  eval : ∀ {s i a t'}, Semantics.Region.Eval O.instr env r s i a t' ↔
    Semantics.Region.Eval O.instr env' t s i a t'
  fault : ∀ {s s'}, Semantics.Region.Fault O.instr O.faults env r s s' ↔
    Semantics.Region.Fault O.instr O.faults env' t s s'
  div : ∀ {s}, Semantics.External.Diverges O.instr O.prim (.region env r s) ↔
    Semantics.External.Diverges O.instr O.prim (.region env' t s)

namespace RegionAt

theorem of_obs {r t : Region Φ} (h : Region.Obs.{u,w,x} r t) : RegionAt O env r env t :=
  ⟨h.eval, h.fault, h.diverges⟩

theorem symm {r t : Region Φ} (h : RegionAt O env r env' t) : RegionAt O env' t env r :=
  ⟨h.eval.symm, h.fault.symm, h.div.symm⟩

theorem trans {r t q : Region Φ} (h : RegionAt O env r env' t) (h' : RegionAt O env' t env'' q) :
    RegionAt O env r env'' q :=
  ⟨h.eval.trans h'.eval, h.fault.trans h'.fault, h.div.trans h'.div⟩

end RegionAt

theorem TermAt.refl (a : Tm Φ) : TermAt O env a env a := ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem TermAt.symm {a b : Tm Φ} (h : TermAt O env a env' b) : TermAt O env' b env a :=
  ⟨h.eval.symm, h.fault.symm, h.div.symm⟩

variable {κ : Type v} [HasTy Φ (Ty κ)]

/-- Native regions are compared on shaped inputs, with arbitrary well-typed
primitive replies and the original fault and divergence relations. -/
@[expose] def ShapedObs (Γ : VCtx (Ty κ)) (r t : Region Φ) : Prop :=
  ∀ (O : Ops Φ α σ) (atomType : α → κ → Prop)
    (_primitive : Resumption.Typing.InstrTyped atomType O.instr)
    (env : Env α), EnvTyped atomType Γ env → RegionAt O env r env t

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Continuation
