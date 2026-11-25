module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Thms

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b c d : CapProfile O}

def FixedDrawing.setoid (S : Signature.{u,v} O) (a b : CapProfile O) :
    Setoid (FixedDrawing S a b) where
  r := FixedDrawing.Equivalent
  iseqv := ⟨FixedDrawing.Equivalent.refl, FixedDrawing.Equivalent.symm, FixedDrawing.Equivalent.trans⟩

/-- Classes for the fixed-cap ambient endpoint relation. -/
def CapClass (S : Signature.{u,v} O) (a b : CapProfile O) :=
  Quotient (FixedDrawing.setoid S a b)

namespace CapClass

def ofDrawing (p : FixedDrawing S a b) : CapClass S a b := Quotient.mk _ p

theorem sound {p q : FixedDrawing S a b} (h : p.Equivalent q) : ofDrawing p = ofDrawing q :=
  Quotient.sound h

noncomputable def thenDo (p : CapClass S a b) (q : CapClass S b c) : CapClass S a c :=
  Quotient.map₂ FixedDrawing.thenDo
    (fun _ _ h _ _ k => FixedDrawing.thenDo_congr h k) p q

theorem thenDo_drawings (p : FixedDrawing S a b) (q : FixedDrawing S b c) :
    thenDo (ofDrawing p) (ofDrawing q) = ofDrawing (p.thenDo q) := by rfl

theorem thenDo_assoc (p : CapClass S a b) (q : CapClass S b c) (r : CapClass S c d) :
    (p.thenDo q).thenDo r = p.thenDo (q.thenDo r) :=
  Quotient.inductionOn₃ p q r (fun p q r => sound (FixedDrawing.thenDo_assoc p q r))

end CapClass
end Silmaril.RuntimeWires.ProgressiveGraph
