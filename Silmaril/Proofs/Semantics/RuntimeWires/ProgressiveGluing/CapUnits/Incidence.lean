module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapUnits.Identity
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Incidence
import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.Proofs.CapUnits

open ProgressiveGraph
open CapClasses (matching match_slot)
open CollarAssociator (leftWire rightWire wire_contact wire_cases left_injective right_injective
  left_label right_label generator_lower generator_upper inputs_lower inputs_upper outputs_lower outputs_upper)

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {a b : CapProfile O}
variable (p : FixedDrawing S a b)

abbrev leftMatch (h : a.Inside) := matching (FixedDrawing.identity S a h) p
abbrev rightMatch (h : b.Inside) := matching p (FixedDrawing.identity S b h)

theorem left_contact (h : a.Inside) (i : Fin a.size) :
    (leftMatch p h).contact ((FixedDrawing.identity S a h).output i) = p.input i :=
  match_slot _ _ i

theorem right_contact (h : b.Inside) (i : Fin b.size) :
    (rightMatch p h).contact (p.output i) = (FixedDrawing.identity S b h).input i :=
  match_slot _ _ i

theorem left_name (h : a.Inside) (i : Fin a.size) :
    leftWire (leftMatch p h) i = rightWire (leftMatch p h) (p.input i).val := by
  have eq := wire_contact (leftMatch p h) ((FixedDrawing.identity S a h).output i)
  rw [left_contact] at eq
  exact eq

theorem right_name (h : b.Inside) (i : Fin b.size) :
    rightWire (rightMatch p h) i = leftWire (rightMatch p h) (p.output i).val := by
  have eq := wire_contact (rightMatch p h) (p.output i)
  rw [right_contact] at eq
  exact eq.symm

def leftVertices (V : ℕ) : Fin V ≃ Fin (0 + V) := finCongr (Nat.zero_add V).symm

theorem leftVertices_apply (V : ℕ) (j : Fin V) : leftVertices V j = Fin.natAdd 0 j := by
  apply Fin.ext
  simp [leftVertices]

def leftIncidence (h : a.Inside) : p.drawing.IncidenceEquiv (leftMatch p h).glue where
  vertex := leftVertices p.vertices
  wire := Equiv.ofBijective (rightWire (leftMatch p h))
    ⟨right_injective _, fun w => by
      rcases wire_cases (leftMatch p h) w with ⟨i, eq⟩ | h'
      · exact ⟨(p.input i).val, (left_name p h i).symm.trans eq⟩
      · exact h'⟩
  generator j :=
    (congrArg (leftMatch p h).glue.generator (leftVertices_apply _ j)).trans (generator_upper _ j)
  label := right_label _
  inputs j :=
    (congrArg (leftMatch p h).glue.inputs (leftVertices_apply _ j)).trans (inputs_upper _ j)
  outputs j :=
    (congrArg (leftMatch p h).glue.outputs (leftVertices_apply _ j)).trans (outputs_upper _ j)

theorem leftIncidence_vertex (h : a.Inside) (j : Fin p.vertices) :
    (leftIncidence p h).vertex j = Fin.natAdd 0 j := leftVertices_apply _ _

def rightIncidence (h : b.Inside) : p.drawing.IncidenceEquiv (rightMatch p h).glue where
  vertex := Equiv.refl _
  wire := Equiv.ofBijective (leftWire (rightMatch p h))
    ⟨left_injective _, fun w => by
      rcases wire_cases (rightMatch p h) w with h' | ⟨i, eq⟩
      · exact h'
      · exact ⟨(p.output i).val, (right_name p h i).symm.trans eq⟩⟩
  generator := generator_lower _
  label := left_label _
  inputs := inputs_lower _
  outputs := outputs_lower _

end Silmaril.RuntimeWires.Proofs.CapUnits
