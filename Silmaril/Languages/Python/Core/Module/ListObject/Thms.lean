module

public import Silmaril.Languages.Python.Core.Module.ListObject.Defs

public section

namespace Silmaril.Languages.Python.Core.Module

theorem ListHeap.allocate_lookup_new (heap : ListHeap) (contents : List Value) :
    let (object, next) := heap.allocate contents
    heap.lookup object.address = none ∧ next.lookup object.address = some contents := by
  simp [ListHeap.allocate, ListHeap.lookup]

theorem ListHeap.allocate_lookup_old (heap : ListHeap) (contents : List Value)
    {address : Nat} (old : address < heap.objects.size) :
    (heap.allocate contents).2.lookup address = heap.lookup address := by
  simp [ListHeap.allocate, ListHeap.lookup, Array.getElem?_push, Nat.ne_of_lt old]

theorem ListHeap.allocate_distinct (heap : ListHeap) (first second : List Value) :
    (heap.allocate first).1.address ≠ ((heap.allocate first).2.allocate second).1.address := by
  simp [ListHeap.allocate]

end Silmaril.Languages.Python.Core.Module
