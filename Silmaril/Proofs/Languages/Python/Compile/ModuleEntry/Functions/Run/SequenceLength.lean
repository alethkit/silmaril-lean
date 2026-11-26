module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.SequenceLength

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module.SeededCall (Namespace)

theorem readSequenceLength_ok_iff (space : Namespace) (length : Nat) (value : Int) :
    readSequenceLength space length = .ok value ↔
      space.lookupGlobal "len" = some (.builtin .len) ∧ value = Int.ofNat length := by
  cases found : space.lookupGlobal "len" with
  | none => simp [readSequenceLength, found]
  | some callee =>
    cases callee with
    | builtin identity => cases identity <;> simp [readSequenceLength, found, eq_comm]
    | _ => simp [readSequenceLength, found]

theorem run_assertSequenceLength {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (test : SequenceLengthTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertSequenceLength test :: rest) =
      let result := readSequenceLength space test.length
      let receipt : CallEvent := ⟨"len", ⟨result.map .int, none⟩⟩
      match result.bind (checkSequenceLengthResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, Core.Module.ListHeap.empty⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest
        { tail with calls := receipt :: tail.calls } := by
  simp only [runInstructionsIn, effectWithLists, effect, assertSequenceLength]
  cases linked : (readSequenceLength space test.length).bind (checkSequenceLengthResult space test) <;> rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.SequenceLength
