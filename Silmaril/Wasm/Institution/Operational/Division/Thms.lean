module

public import Silmaril.Wasm.Institution.Operational.Division.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.Division.Rules
import Silmaril.Proofs.Wasm.Institution.Operational.Division.Bridge

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Division

open CategoryTheory Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {s t : Config H}

/-- Every derivation starts and ends inside the instruction guard. -/
theorem derives_admitted (h : DerivesEdge s t) : Admitted s ∧ Admitted t :=
  Proofs.derives_admitted h

theorem derives_sound (h : DerivesEdge s t) : Step P noHost s t :=
  Proofs.derives_sound h

/-- Exact native reduction from an admitted source, with an arbitrary target. -/
theorem derives_edge_iff (supported : Admitted s) : DerivesEdge s t ↔ Step P noHost s t :=
  ⟨derives_sound, Proofs.step_readback supported⟩

/-- The guard is forward-closed. All native successors of admitted sources
are kept, including intermediate trap propagation states. -/
theorem step_closed (supported : Admitted s) (step : Step P noHost s t) : Admitted t :=
  (derives_admitted ((derives_edge_iff supported).mpr step)).2

/-- Admission is the only source of boundary-policy UB. -/
theorem policy_safe (supported : Admitted s) : (policy H).SafeAt s :=
  Proofs.policy_safe supported

/-- The existing Core system with arbitrary transition state maps. -/
abbrev coreTransitions (P : Profile) (H : Type) : TransitionSystem :=
  ⟨WasmShape.signatures.obj (Operational.shape H), (Operational.system P (noHost (H := H))).model⟩

/-- Core steps restricted at the source. Closure also restricts their targets. -/
def guardedCore (P : Profile) (H : Type) : TransitionSystem :=
  ⟨(coreTransitions P H).shape,
    fun e => Admitted (decode e.1) ∧ (coreTransitions P H).model e⟩

/-- The adapter uses the original Core configuration encoding and keeps unit labels. -/
def toCore (P : Profile) (H : Type) : transitionSystem H ⟶ coreTransitions P H :=
  ⟨⟨encode, id⟩, fun h => derives_sound h⟩

/-- Encoding and decoding give inverse step-preserving maps for the guarded system. -/
def guardedIso (P : Profile) (H : Type) : transitionSystem H ≅ guardedCore P H where
  hom := ⟨⟨encode, id⟩, fun h => ⟨(derives_admitted h).1, derives_sound h⟩⟩
  inv := ⟨⟨decode, id⟩, fun h => (derives_edge_iff h.1).mpr h.2⟩
  hom_inv_id := System.Hom.ext rfl
  inv_hom_id := System.Hom.ext rfl

/-- An ordinary Core edge atom and its SOS edge atom agree at an admitted source. -/
theorem atom_iff (supported : Admitted s) :
    (WasmShape.institution.obj (Operational.shape H)).Sat
        (Discrete.mk (coreTransitions P H).model) (encode s, (), encode t) ↔
      (SOS.Shape.institution.obj (shape H)).Sat (Discrete.mk (presentation H).Derives)
        (.atom (s, t)) :=
  (Operational.step_iff P noHost s t).trans (derives_edge_iff supported).symm

/-- All finite native runs from an admitted source read back with the same
labels and intermediate states via the lossless encoding. -/
theorem runs_iff (supported : Admitted s) (labels : List Unit) :
    Runs (transitionSystem H).model s labels t ↔
      Runs (coreTransitions P H).model (encode s) labels (encode t) :=
  ⟨fun h => List.map_id labels ▸
    (show Runs (coreTransitions P H).model (encode s) (labels.map id) (encode t) from
      System.Hom.runs (toCore P H) h),
    fun h => Proofs.runs_readback h supported⟩

end Silmaril.Wasm.Institution.Operational.Division
