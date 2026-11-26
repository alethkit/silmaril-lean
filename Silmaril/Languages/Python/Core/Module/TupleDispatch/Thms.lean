module

public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs

public section

namespace Silmaril.Languages.Python.Core.Module.TupleDispatch

theorem materialize_empty (heap : Heap) : heap.materialize [] = (⟨none, []⟩, heap) := rfl

theorem concat_empty_left (heap : Heap) (left right : Object) (empty : left.contents = []) :
    concat heap left right = (right, heap) := by simp [concat, empty]

theorem concat_empty_right (heap : Heap) (left right : Object) (nonempty : left.contents ≠ [])
    (empty : right.contents = []) : concat heap left right = (left, heap) := by
  simp [concat, nonempty, empty]

theorem concat_nonempty (heap : Heap) (left right : Object)
    (leftPresent : left.contents ≠ []) (rightPresent : right.contents ≠ []) :
    concat heap left right =
      (⟨some heap.objects.size, left.contents ++ right.contents⟩,
        ⟨heap.objects.push (left.contents ++ right.contents)⟩) := by
  cases left with | mk address contents => cases contents <;> simp_all [concat, Heap.materialize]

theorem callUnbound_lookup_failure (heap : Heap) (binding : Option TypeBinding) (method : Method)
    (receiver argument : Literal) (error : Failure) (failed : lookupUnbound binding method = .error error) :
    callUnbound heap binding method receiver argument = (.error error, heap) := by simp [callUnbound, failed]

/-- Descriptor checking happens after the second argument has been prepared. -/
theorem callUnbound_list_receiver (heap : Heap) (method : Method)
    (receiver : List Core.Module.Value) (argument : Literal) :
    callUnbound heap (some .stockTuple) method (.list receiver) argument =
      (.error (.wrongReceiver method), (argument.prepare heap).2) := rfl

theorem direct_eq_list (heap : Heap) (receiver : Object) (argument : List Core.Module.Value) :
    (BoundMethod.mk .eq receiver).invoke heap (.list argument) = (.ok .notImplemented, heap) ∧
      equal receiver (.list argument) = false := ⟨rfl, rfl⟩

end Silmaril.Languages.Python.Core.Module.TupleDispatch
