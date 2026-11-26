module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.ITree.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Infinite.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified

open Silmaril.SSA.LambdaRTL Silmaril.Isotope Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi (runTree)
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Diverges Env)
open LambdaSSA.Semantics.Interaction (Primitive region)
open LetCase.LocallyNameless (Tm)

universe u v w
variable {n : Nat}

section Lowering

variable {V K Base : Type u} {F : Type v} [DecidableEq V] [DecidableEq K]
  [HasTy F (Ty Base)]
variable {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
  {admitted : Admission source inputs captures β R L}

private theorem lowered (admitted : Admission source inputs captures β R L) :
    CFG.Cyclic.Phi.compile source = some (CFG.Cyclic.Versioning.compile (CFG.Cyclic.Phi.lower source)) :=
  (CFG.Cyclic.Phi.compile_eq_some_iff _ _).mpr ⟨admitted.wellFormed.normalized, rfl⟩

end Lowering

private theorem capture_at {W α : Type w} (names : Fin n → Option W) (store : W → Value α) (i : Fin n) :
    captureEnv names store i.val = CFG.Cyclic.Phi.liftStore .unit store (names i) := by
  simp [captureEnv, i.isLt, CFG.Cyclic.Phi.liftStore]

section Atomic

variable {V K Base F α : Type u} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
  {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
  {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
  {admitted : Admission source inputs captures β R L} {packetInput : Tm Empty F 0}
  (closed : Closed admitted packetInput) (prim : F → Value α → Part (Value α))
  (store : V → Value α) (ambient : Env α)

theorem packed_run_iff {value : Value α}
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient
      (Morphism.CaseSSA.erase packetInput) () v state ↔
        v = Capture.packEnv n (captureEnv captures store) ∧ state = ()) :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source store ↔
      LambdaSSA.Semantics.Region.Eval (instr prim) ambient (FiniteCFG.packedExecutionRegion closed.typed)
        () 0 (Region.packedExitValue 0 value) () :=
  NamedFlat.Phi.packed_run_iff (lowered admitted) admitted.elaborated (capture_at captures store)
    closed.typed closed.closes packet

theorem packed_infinite_run_iff
    (packet : ∀ v state, LambdaSSA.Semantics.Tm.Eval (instr prim) ambient
      (Morphism.CaseSSA.erase packetInput) () v state ↔
        v = Capture.packEnv n (captureEnv captures store) ∧ state = ()) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source store ↔
      Diverges (instr prim) (.region ambient (FiniteCFG.packedExecutionRegion closed.typed) ()) :=
  NamedFlat.Phi.packed_infinite_run_iff (lowered admitted) admitted.elaborated (capture_at captures store)
    closed.typed closed.closes packet

end Atomic

theorem packed_run_tree {Events : Type w → Type w} {F : Type v}
    {V K Base α Reply : Type (w + 1)} [DecidableEq V] [DecidableEq K] [HasTy F (Ty Base)]
    {source : CFG.Cyclic.Phi.Graph V K F} {inputs : List V} {captures : Fin n → Option V}
    {β : BoundCtx (Ty Base) n} {R : Fin (blockCount source) → Ty Base} {L : Fin 1 → Ty Base}
    {admitted : Admission source inputs captures β R L} {packetInput : Tm Empty F 0}
    (closed : Closed admitted packetInput) (instr : Primitive Events F α)
    (produce : Tree Events Reply) (store : Reply → V → Value α) (ambient : Env α)
    (packet : LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase packetInput) =
      (produce >>= fun reply => pure (Capture.packEnv n (captureEnv captures (store reply))))) :
    region instr ambient (FiniteCFG.packedExecutionRegion closed.typed) =
      (produce >>= fun reply => runTree instr source (store reply) >>= fun p =>
        pure (FiniteCFG.packedTreeOutput (treeExitNumber [none] p))) :=
  NamedFlat.Phi.packed_run_tree instr captures store (lowered admitted) admitted.elaborated
    (fun reply => capture_at captures (store reply)) closed.typed closed.closes packet

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified
