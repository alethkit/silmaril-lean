module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CapClasses.Matching

public section

namespace Silmaril.RuntimeWires.Proofs.CapClasses

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O}
variable {a b c d : CapProfile O}

theorem compare_matches {L M R A B C : ℕ}
    {x : ProgressiveGraph.Diagram S L A .point} {y : ProgressiveGraph.Diagram S M B .point}
    {z : ProgressiveGraph.Diagram S R C .point}
    (m : x.OrderedVerticalMatch y) (n : y.OrderedVerticalMatch z)
    (left : m.glue.OrderedVerticalMatch z) (right : x.OrderedVerticalMatch n.glue)
    (h : left = m.attachAfter n) (k : right = m.attachBefore n) :
    Nonempty (left.glue.CapComparison right.glue) := by
  subst left
  subst right
  exact ⟨assoc_comparison m n⟩

theorem glue_assoc (p : FixedDrawing S a b) (q : FixedDrawing S b c) (r : FixedDrawing S c d) :
    (glue (glue p q) r).Equivalent (glue p (glue q r)) := by
  have result := compare_matches (x := p.drawing) (y := q.drawing) (z := r.drawing)
    (matching p q) (matching q r) (matching (glue p q) r) (matching p (glue q r))
    (match_after p q r) (match_before p q r)
  unfold FixedDrawing.Equivalent
  with_reducible exact result

end Silmaril.RuntimeWires.Proofs.CapClasses
