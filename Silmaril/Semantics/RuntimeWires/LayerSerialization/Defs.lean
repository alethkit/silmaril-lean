module

public import Silmaril.Semantics.RuntimeWires.ProgressiveSimultaneous.Thms
public import Mathlib.Data.Finset.Insert

@[expose] public section

/-!
# Serial schedules of a progressive layer

An algebraic comparison for Definition 3.2, Figure 7 and Lemma 3.4
(pp. 9:6–9:7) of Mario Román and Paweł Sobociński, *String Diagrams for
Premonoidal Categories*, arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram

open Silmaril.RuntimeWires.Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V W : ℕ} {kind : VertexSeparation}
variable (d : Diagram S V W kind)

def vertexWord (j : Fin V) : Bool → List O
  | false => S.source (d.generator j)
  | true => S.target (d.generator j)

/-- Read the current frontier in the original horizontal slot order, using
the output word precisely at the completed vertex slots. -/
def frontier (done : Finset (Fin V)) : List (LayerSlot V W) → List O
  | [] => []
  | .inl w :: tail => d.label w :: frontier done tail
  | .inr j :: tail => d.vertexWord j (decide (j ∈ done)) ++ frontier done tail

/-- Pass an unchanged vertex block or execute the newly completed vertex. -/
def vertexStep (j : Fin V) (a b : Bool) (h : a = true → b = true) {A B : List O}
    (tail : Row S A B) : Row S (d.vertexWord j a ++ A) (d.vertexWord j b ++ B) :=
  match a, b with
  | false, false => Row.pass (S.source (d.generator j)) tail
  | false, true => .box (d.generator j) tail
  | true, true => Row.pass (S.target (d.generator j)) tail
  | true, false => (Bool.noConfusion (h rfl))

/-- Execute precisely the newly completed vertices, in their fixed
horizontal slots, and pass through every other current block. -/
def layerStep {done next : Finset (Fin V)} (h : done ⊆ next) :
    (slots : List (LayerSlot V W)) → Row S (d.frontier done slots) (d.frontier next slots)
  | [] => .empty
  | .inl w :: tail => .wire (d.label w) (layerStep h tail)
  | .inr j :: tail =>
    d.vertexStep j (decide (j ∈ done)) (decide (j ∈ next))
      (fun ha => decide_eq_true (h (of_decide_eq_true ha))) (layerStep h tail)

/-- The set of completed slots after executing the schedule. -/
def completed (done : Finset (Fin V)) (order : List (Fin V)) : Finset (Fin V) :=
  order.foldl (fun finished j => insert j finished) done

/-- Serialize by inserting one vertex ID into the completed set at each
step. Each recursive seam is indexed by the same new set on both sides. -/
def serializeFrom (slots : List (LayerSlot V W)) (done : Finset (Fin V)) :
    (order : List (Fin V)) →
      Sheet S (d.frontier done slots) (d.frontier (completed done order) slots)
  | [] => .empty _
  | j :: tail =>
    .cons (d.layerStep (Finset.subset_insert j done) slots)
      (serializeFrom slots (insert j done) tail)

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram
