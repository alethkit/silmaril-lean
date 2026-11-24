module

import Silmaril.Logic.Operational.Machines.Thms
import Silmaril.Wasm.Institution.Operational.Thms
import Silmaril.X86.OperationalInstitution.Thms

open CategoryTheory Silmaril.Logic.Operational Silmaril.Logic.Institution

private abbrev counterSig : Signature := ⟨Nat, Bool⟩

private def counterModel : counterSig.Model :=
  fun e => e.2.2 = e.1 + 1

private abbrev counter : TransitionSystem := ⟨counterSig, counterModel⟩

private def shift : counter ⟶ counter where
  shape := (⟨Nat.succ, Bool.not⟩ : counterSig ⟶ counterSig)
  preserves := by
    rintro ⟨s, _, t⟩ h
    change (t : Nat) = Nat.succ s at h
    change Nat.succ t = Nat.succ (Nat.succ s)
    rw [h]

private theorem twoSteps : Runs counterModel 0 [true, false] 2 :=
  .stepL (show counterModel (0, true, 1) from rfl)
    (.stepL (show counterModel (1, false, 2) from rfl) .refl)

example : Runs counterModel 1 [false, true] 3 :=
  System.Hom.runs shift twoSteps

example : Runs counterModel 2 [true, false] 4 :=
  System.Hom.runs (shift ≫ shift) twoSteps

private abbrev registers : RegisterShape := ⟨Unit, Bool, Nat, Bool, Nat, Unit⟩

private def registerView : registers ⟶ registers :=
  ⟨id, Bool.not, Nat.succ, Bool.not, Nat.succ, id⟩

private def config : registers.Config :=
  ⟨(), (fun b => if b then 7 else 8), (fun b => if b then some 42 else none)⟩

example : (RegisterShape.mapConfig registerView config).registers false = 8 := rfl
example : (RegisterShape.mapConfig registerView config).memory false = some 43 := rfl
example : (RegisterShape.mapConfig registerView config).memory true = none := rfl

example (M : (RegisterShape.institution.obj registers).Mod)
    (e : (RegisterShape.institution.obj registers).Sen) :
    (RegisterShape.institution.obj registers).Sat M ((RegisterShape.institution.map registerView).sen e) ↔
      (RegisterShape.institution.obj registers).Sat ((RegisterShape.institution.map registerView).mod.obj M) e :=
  satisfaction_condition RegisterShape.institution registerView M e

private abbrev stack : StackShape := ⟨Unit, Nat, Unit⟩

private def bump : stack ⟶ stack := ⟨id, Nat.succ, id⟩

example : (StackShape.mapConfig (bump ≫ bump) ⟨(), [2, 1]⟩).stack = [4, 3] := rfl

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics in
example {H : Type} (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) :
    (Silmaril.Wasm.Institution.Operational.system P host).model
      (Silmaril.Wasm.Institution.Operational.encode ⟨s, f, [.plain .nop]⟩, (),
        Silmaril.Wasm.Institution.Operational.encode ⟨s, f, []⟩) :=
  (Silmaril.Wasm.Institution.Operational.step_iff P host _ _).2 (.parametric .nop)

open Silmaril.X86.OperationalInstitution in
example {σ : Type} (A : Silmaril.X86.RelIsa σ) (s : σ) (live : A.live s) (stop : A.step s .stop) :
    (system A).model (encode A.toViews (some s), (), encode A.toViews none) :=
  (stop_iff A s).2 ⟨live, stop⟩
