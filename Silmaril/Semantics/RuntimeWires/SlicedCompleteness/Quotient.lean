module

public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Encoding
import Silmaril.Proofs.Semantics.RuntimeWires.SlicedCompleteness.Algebra

@[expose] public section

namespace Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {A B C X Y : List O}

/-- The free monoidal presentation has no extra equations. -/
abbrev noEquations (S : Signature.{u,v} O) : Diagram.Equations S :=
  fun _ _ => False

/-- Morphisms of sliced diagrams modulo the independently defined seam moves. -/
def SeamHom (S : Signature.{u,v} O) (A B : List O) :=
  Quotient (Relation.EqvGen.setoid (Sheet.Move S : Sheet S A B → Sheet S A B → Prop))

namespace SeamHom

def ofSheet (p : Sheet S A B) : SeamHom S A B := Quotient.mk'' p

def id (A : List O) : SeamHom S A A := ofSheet (.empty A)

/-- Composition of seam classes glues matching frontiers. -/
def comp (p : SeamHom S A B) (q : SeamHom S B C) : SeamHom S A C :=
  Quotient.map₂ Sheet.thenDo (fun _ _ hp _ _ hq => by
    exact Proofs.SlicedCompleteness.seam_then hp hq) p q

/-- The tensor induced by placing sheets side by side. -/
def tensor (p : SeamHom S A B) (q : SeamHom S X Y) : SeamHom S (A ++ X) (B ++ Y) :=
  Quotient.map₂ Sheet.tensor (fun _ _ hp _ _ hq => by
    exact Proofs.SlicedCompleteness.seam_tensor hp hq) p q

/-- Interpret seam classes as morphisms of the free monoidal term quotient. -/
def toTermHom (p : SeamHom S A B) : Diagram.Hom S (noEquations S) A B :=
  Quotient.lift (Sheet.denote (noEquations S)) (fun _ _ h => Sheet.SeamEquivalent.sound h _) p

/-- Schedule a free monoidal term as a sheet, descending to a map of quotients. -/
def fromTermHom (f : Diagram.Hom S (noEquations S) A B) : SeamHom S A B :=
  Quotient.lift (fun t => ofSheet (Sheet.encode t))
    (fun _ _ h => Quotient.sound (by exact Proofs.SlicedCompleteness.encode_congr h)) f

end SeamHom
end Silmaril.RuntimeWires.Sliced
