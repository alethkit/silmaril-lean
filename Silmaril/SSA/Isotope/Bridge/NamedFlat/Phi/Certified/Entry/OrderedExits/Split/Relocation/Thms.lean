module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.ReverseAcceptance.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Relocation

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Reverse (Register Registers Lowered numberedInterface lower lowerChecked withLiveOut)

universe u v

/-- Successful inference preserves every requested physical name and keeps
all local depths distinct and outside the input and parameter registers.
Unconstrained depths also avoid registers written by the original output. -/
theorem Relocation.infer_valid (captures : Nat) (parameter : Register.{u}) (previous : List Register.{u})
    (needed : List Relocation.Demand.{u}) {allocation : Registers Register.{u}}
    (found : Relocation.infer captures parameter previous needed = some allocation) :
    Relocation.Valid captures parameter previous needed allocation :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Relocation.infer_valid
    captures parameter previous needed found

variable {κ V W K : Type (u + 1)} {n : Nat} [DecidableEq V] [DecidableEq W] [DecidableEq K]
  {P : FlatInstitution.Signature.{u, v} κ} [DecidableEq P.Instr]
  {context : BoundCtx (Ty κ) n} {exits : List (Option K)} {external : Fin exits.length → Ty κ}
  {fields : Option K → List (Register × Ty κ)} {C : Captures V context} {plan : Plan V W K K}
  {a : Admission P (numberedInterface context exits external) fields C}

local notation "Ports" => numberedInterface context exits external

/-- The recovered allocation satisfies the ordered requests of the actual
admitted split table, including repeated requests across different blocks. -/
theorem GeneratedSplit.relocatedRegisters_valid (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    {allocation : Registers Register} (found : split.relocatedRegisters seed = some allocation) :
    ∃ needed, split.relocationDemands seed = some needed ∧
      Relocation.Valid n seed.registers.parameter (Relocation.writtenRegisters seed.output.source) needed allocation := by
  obtain ⟨needed, requests, solved⟩ := Option.bind_eq_some_iff.mp found
  exact ⟨needed, requests, Relocation.infer_valid _ _ _ _ solved⟩

/-- The inferred reverse result is the actual emission at the recovered
allocation. Exact readback includes the declared field order at each exit. -/
theorem GeneratedSplit.reverseRelocated_spec (split : GeneratedSplit plan a) (seed : ReverseSeed a)
    (labels : Fin (Versioning.compile (Phi.OrderedExits.lower split.target.source)).blocks.length → Option K)
    {output : Lowered Ports fields split.target.code}
    (accepted : split.reverseRelocated seed labels = some output) :
    ∃ allocation, split.relocatedRegisters seed = some allocation ∧
      lower allocation (Ports).names labels (fun i => exits[i]) split.target.code = some output.source ∧
      NamedFlat.elaborateAt (withLiveOut fields output.source) exits (Ports).names _ output.count =
        some split.target.code := by
  obtain ⟨allocation, inferred, checked⟩ := Option.bind_eq_some_iff.mp accepted
  exact ⟨allocation, inferred, NamedFlat.Entry.Reverse.lowerChecked_emitted checked, output.readback⟩

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
