module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Defs
public import Silmaril.Semantics.RuntimeWires.Sliced.Thms

@[expose] public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O}

/-- Schedule the tensor of terms by placing all rows from the left factor first. -/
def Sheet.encode : {A B : List O} → Diagram S A B → Sheet S A B
  | _, _, .id A => .empty A
  | _, _, .gen e => .generator e
  | _, _, .comp f g => (encode f).thenDo (encode g)
  | _, _, .tensor f g => (encode f).tensor (encode g)

end Silmaril.RuntimeWires.Sliced
