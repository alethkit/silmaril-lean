module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity.Defs
public import Silmaril.Languages.Python.Core.Closure.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity

open Core.Closure (Heap Value)

theorem identify_empty (heap : Heap) : identify heap (.tuple []) = some .empty := rfl

theorem identify_allocation (heap : Heap) (head : Core.Module.Value) (tail : List Core.Module.Value) :
    let (cell, reached) := heap.allocate (.tuple (head :: tail))
    identify reached (.tupleObject ⟨some cell.address, head :: tail⟩) = some (.allocated cell.address) := by
  simp [identify, Heap.allocate, Heap.lookup, Heap.reserve]

theorem identify_missing {heap : Heap} {address : Nat} (head : Core.Module.Value) (tail : List Core.Module.Value)
    (missing : heap.lookup ⟨address⟩ = none) :
    identify heap (.tupleObject ⟨some address, head :: tail⟩) = none := by
  simp [identify, missing]

theorem compare_identified (heap : Heap) (left right : Operand) (operator : Core.Module.IdentityOperator)
    {first second : Value} {one two : Identity}
    (identifiedFirst : identify heap first = some one) (identifiedSecond : identify heap second = some two) :
    (Test.mk left operator right).compare heap first second =
      some (match operator with | .is_ => decide (one = two) | .isNot => !decide (one = two)) := by
  cases operator <;> simp [Test.compare, identifiedFirst, identifiedSecond]

theorem evaluate_left_failure {ε : Type} (test : Test) (heap : Heap)
    (lookup : String → Except ε (Option Value)) (unsupported : ε) {error : ε}
    (failed : test.left.read lookup = .error error) :
    test.evaluate heap lookup unsupported = .error error := by
  simp [Test.evaluate, failed]; rfl

theorem evaluate_right_failure {ε : Type} (test : Test) (heap : Heap)
    (lookup : String → Except ε (Option Value)) (unsupported : ε) {first : Option Value} {error : ε}
    (read : test.left.read lookup = .ok first) (failed : test.right.read lookup = .error error) :
    test.evaluate heap lookup unsupported = .error error := by
  simp [Test.evaluate, read, failed]; rfl

theorem evaluate_same_opaque_read {ε : Type} (heap : Heap) (lookup : String → Except ε (Option Value))
    (unsupported : ε) {name : String} {head : Core.Module.Value} {tail : List Core.Module.Value}
    (found : lookup name = .ok (some (.tuple (head :: tail)))) :
    (Test.mk (.global name) .is_ (.global name)).evaluate heap lookup unsupported = .ok true := by
  simp [Test.evaluate, Operand.read, found, Bind.bind, Except.bind, Test.compare, identify, sameOpaqueRead]

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.TupleIdentity
