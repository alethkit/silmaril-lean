module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Defs

/-! # A routed producer with a mixed structured consumer -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed

open Isotope.LambdaSSA (Region)
open NestedTheta.ExplicitRuntime (EntryChecked)
open Numbered.Recognize (opcodeCode)
open StructuredCFG.WithNestedFeedback.Reverse.Recursive (Normal Layout decodeLayout expect parse scan weight)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A E M D : τ}
variable {ps : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- Two canonical mixed components with a heterogeneous producer exit.
The consumer has its own numbered scope inside the selected γ arm. -/
structure Components (Φ : Type u) [HasTy Φ τ] (A E M D : τ)
    (ps : List (Ports (OrderedRuntime.Structured.Ty τ))) where
  H : τ
  producer : Normal Φ A E M H E M ps
  rows : List (Ports (OrderedRuntime.Structured.Ty τ))
  consumer : Normal Φ M E D M E D rows

def Components.Supported (s : Components Φ A E M D ps) : Prop :=
  s.producer.Supported ∧ s.consumer.Supported

def Components.source (s : Components Φ A E M D ps) : Fragment Φ A E D :=
  Flat.linkBy s.producer.toSyntax.source s.consumer.toSyntax.source routing

abbrev RoutedGraph (Φ : Type u) [HasTy Φ τ] (A E M D : τ)
    (ps : List (Ports (OrderedRuntime.Structured.Ty τ))) :=
  Graph Φ A E M M E D (ps ++ Selection M E D)

def Components.code (s : Components Φ A E M D ps) :
    Code Φ A E M M E D (ps ++ Selection M E D) :=
  splice s.producer.toSyntax.code s.consumer.toSyntax.code

def Components.graph (s : Components Φ A E M D ps) : RoutedGraph Φ A E M D ps :=
  s.code.1.toGraph

def Components.checked (s : Components Φ A E M D ps) :
    EntryChecked (a := payloadData A E M) (b := payloadData M E D) s.graph.toTerm :=
  s.code.2.collect

/-- Find the final outer route and γ. Forks inside the producer remain
part of its prefix, and the consumer is read within the second child. -/
def splitLayout [DecidableEq τ] (E M D : τ) (labels : Layout τ Φ) :
    Option (τ × Layout τ Φ × Layout τ Φ) :=
  match labels.reverse with
  | .fork [] consumer :: .route h e m d :: producer =>
    if (e, m, d) = (E, M, D) then some (h, producer.reverse, consumer) else none
  | _ => none

/-- Parse both components from the input graph. The layout fixes only the
outer signature index of the producer prefix and the external interface. -/
def candidate [DecidableEq τ] (g : RoutedGraph Φ A E M D ps) : Option (Components Φ A E M D ps) := do
  let (h, producerLabels, arm) ← (scan g.toTerm).bind (splitLayout E M D)
  let producer ← decodeLayout (A := A) (X := E) (Z := M) (L := h) (E := E) (D := M) (sigs := ps) producerLabels
  let ⟨rows, consumer⟩ ← expect (← parse (weight arm) M E D arm) M E D
  return ⟨h, producer, rows, consumer⟩

inductive Related (g : RoutedGraph Φ A E M D ps) : Region Φ → Type u where
  | generated (s : Components Φ A E M D ps) (wiring : s.graph = g) : Related g s.source.region

abbrev Fibre (g : RoutedGraph Φ A E M D ps) :=
  Σ r : Region Φ, Related g r

theorem Related.typing {g : RoutedGraph Φ A E M D ps} {r : Region Φ} (w : Related g r) :
    Region.HasType [A] r [E,D] :=
  match w with | .generated s _ => s.source.typing

/-- Certify the entire re-emission, including both sides of the routed cut,
all child captures and the token entering the selected arm. -/
def certify [DecidableEq τ] [DecidableEq Φ] (g : RoutedGraph Φ A E M D ps) (s : Components Φ A E M D ps) :
    Option (Fibre g) :=
  letI := NestedTheta.Equality.decideGraph (opcodeCode (τ := τ) (Φ := Φ)) s.graph g
  if wiring : s.graph = g then some ⟨s.source.region, .generated s wiring⟩ else none

def recover [DecidableEq τ] [DecidableEq Φ] (g : RoutedGraph Φ A E M D ps) : Option (Fibre g) :=
  (candidate g).bind (certify g)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed
