module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Defs

/-! # Block-local simulation for independent predecessor-indexed φ graphs -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending)
open Silmaril.Elgot (mapReturn)
open Silmaril.Elgot.ITree (Tree vis diverge)
open LambdaSSA.FiniteCFG (packedTreeOutput)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)

universe u v w
variable {Events : Type u → Type u} {V W K J α : Type (u + 1)}
  {F : Type v} {G : Type w}

abbrev BodyResult (V K α : Type (u + 1)) := Transfer α ⊕ Pending V K (Value α)

noncomputable def entryTree [DecidableEq V] (instr : Primitive Events F α) (graph : Graph V K F)
    (store : V → Value α) : Tree Events (BodyResult V K α) :=
  Sum.inr <$> CFG.Cyclic.Phi.execute (treeModel instr) none graph.entry store

/-- The actual simultaneous φ step, with the same exit encoding as the
packed observation. Internal returns retain the predecessor and outgoing store. -/
noncomputable def stepTree [DecidableEq V] [DecidableEq K] (instr : Primitive Events F α)
    (graph : Graph V K F) : Pending V K (Value α) → Tree Events (BodyResult V K α) :=
  mapReturn (CFG.Cyclic.Phi.step (treeModel instr) graph)
    (fun exit => pure (packedTreeOutput (treeExitNumber [none] exit)))

variable {A B : Type (u + 1)}

/-- Follow finitely many silent internal transfers before inspecting a body.
The witness cannot pass a visible request or an external return. -/
inductive Silent (step : A → Tree Events (B ⊕ A)) :
    Tree Events (B ⊕ A) → Tree Events (B ⊕ A) → Prop where
  | refl (t) : Silent step t t
  | more {p t} : Silent step (step p) t → Silent step (pure (.inr p)) t

variable {C : Type (u + 1)}

/-- A single local inspection. The right may take a finite silent prefix to
match an exit, a request, or a paired edge. An unpaired left transfer takes
one actual left step before consulting the residual relation again. -/
inductive Layer (leftStep : A → Tree Events (B ⊕ A)) (rightStep : C → Tree Events (B ⊕ C))
    (boundary : A → C → Prop)
    (residual : Tree Events (B ⊕ A) → Tree Events (B ⊕ C) → Prop) :
    Tree Events (B ⊕ A) → Tree Events (B ⊕ C) → Prop where
  | diverged (right) : Layer leftStep rightStep boundary residual diverge right
  | exit {value right} (silent : Silent rightStep right (pure (.inl value))) :
      Layer leftStep rightStep boundary residual (pure (.inl value)) right
  | request {R : Type u} (event : Events R) {leftNext rightNext right}
      (silent : Silent rightStep right (vis event rightNext))
      (replies : ∀ reply, residual (leftNext reply) (rightNext reply)) :
      Layer leftStep rightStep boundary residual (vis event leftNext) right
  | edge {leftPending rightPending right}
      (silent : Silent rightStep right (pure (.inr rightPending)))
      (paired : boundary leftPending rightPending) :
      Layer leftStep rightStep boundary residual (pure (.inr leftPending)) right
  | leftTransfer {leftPending right next}
      (silent : Silent rightStep right next) (related : residual (leftStep leftPending) next) :
      Layer leftStep rightStep boundary residual (pure (.inr leftPending)) right

/-- A graph-local proof witness. The boundary relation can include label
alignment, type invariants, and live register agreements. For a paired jump,
`atBoundary` checks the bodies after their actual predecessor-indexed,
parallel assignments. `inspect` works on local trees and reply continuations. -/
structure Simulation [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
    (leftPrim : Primitive Events F α) (rightPrim : Primitive Events G α)
    (left : Graph V K F) (right : Graph W J G) where
  boundary : Pending V K (Value α) → Pending W J (Value α) → Prop
  residual : Tree Events (BodyResult V K α) → Tree Events (BodyResult W J α) → Prop
  atBoundary {l r} : boundary l r → residual (stepTree leftPrim left l) (stepTree rightPrim right r)
  inspect {l r} : residual l r →
    Layer (stepTree leftPrim left) (stepTree rightPrim right) boundary residual l r

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
