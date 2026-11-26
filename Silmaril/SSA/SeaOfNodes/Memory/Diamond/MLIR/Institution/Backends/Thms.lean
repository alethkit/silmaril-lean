module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.ToRVSDG.Thms

/-! Read the same two-cell return in each existing backend's encoding. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution

open CategoryTheory
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution renaming
  Signature → EntrySignature, Equation → NativeEquation
open Isotope.Institution.Observational (ssaBeh)

variable {P : EntrySignature}

/-- The MLIR word and both cells agree with the λSSA room's encoded return. -/
theorem observe_iff_lambdaSSA (graph : Graph P.args) (input : Valuation P)
    (guard : Bool) (initial : Heap 2) (word : Word) (final : Heap 2) :
    (emit graph).observe input guard initial = some (encodeResult word final) ↔
      LambdaSSA.Institution.returnObservation initial (word, final) ∈
        ssaBeh 1 (LambdaSSA.Institution.entryModel (nativeModel input) guard)
          (LambdaSSA.Institution.scope graph) :=
  (observe_iff_returns graph input guard initial word final).trans
    (LambdaSSA.Institution.ret_mem_returns graph (nativeModel input) guard initial word final).symm

/-- The MLIR word and both cells agree with the numbered γ output tuple. -/
theorem observe_iff_rvsdg (graph : Graph P.args) (input : Valuation P)
    (guard : Bool) (initial : Heap 2) (word : Word) (final : Heap 2) :
    (emit graph).observe input guard initial = some (encodeResult word final) ↔
      (Diamond.Institution.ToRVSDG.Program.ofGraph graph).observe (nativeModel input) guard initial =
        Memory.encodeResult word final :=
  (observe_iff_returns graph input guard initial word final).trans
    (Diamond.Institution.ToRVSDG.observe_iff_returns graph (nativeModel input) guard initial word final).symm

theorem lambdaSSA_satisfaction (e : NativeEquation P) (input : Valuation P) :
    (room P).Sat (Discrete.mk input) (translateEquation e) ↔
      ∀ guard, (LambdaSSA.Institution.room P).Sat
        (Discrete.mk (LambdaSSA.Institution.entryModel (nativeModel input) guard))
        (LambdaSSA.Institution.translateEquation e) :=
  (translated_satisfaction e input).trans
    (LambdaSSA.Institution.translated_satisfaction e (nativeModel input)).symm

theorem rvsdg_satisfaction (e : NativeEquation P) (input : Valuation P) :
    (room P).Sat (Discrete.mk input) (translateEquation e) ↔
      (Diamond.Institution.ToRVSDG.room P).Sat (Discrete.mk (nativeModel input))
        (Diamond.Institution.ToRVSDG.translateEquation e) :=
  (translated_satisfaction e input).trans
    (Diamond.Institution.ToRVSDG.translated_satisfaction e (nativeModel input)).symm

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.MLIR.Institution
