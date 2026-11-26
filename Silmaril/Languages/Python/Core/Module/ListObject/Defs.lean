module

public import Silmaril.Languages.Python.Core.Module.Defs

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module

/-- Identity within the module's list allocation table, with exact scalar contents. -/
structure ListObject where
  address : Nat
  contents : List Value
  deriving DecidableEq, Repr

/-- Allocated lists remain available for observation in allocation order. -/
structure ListHeap where
  objects : Array (List Value)
  deriving DecidableEq, Repr

def ListHeap.empty : ListHeap := ⟨#[]⟩

def ListHeap.lookup (heap : ListHeap) (address : Nat) : Option (List Value) :=
  heap.objects[address]?

def ListHeap.allocate (heap : ListHeap) (contents : List Value) : ListObject × ListHeap :=
  (⟨heap.objects.size, contents⟩, ⟨heap.objects.push contents⟩)

end Silmaril.Languages.Python.Core.Module
