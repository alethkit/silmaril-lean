module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Observations.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs

/-! # A numbered RVSDG for the conditional-loop flat handoff -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered

open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime (EntryChecked Checked)
open NestedTheta.ExplicitRuntime.Splice (Code append)
open TwoBlock.TwoExit (Pure)
open LinearChain.Wiring (newest)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I B K M C J E D : τ}

abbrev Start (I M : τ) := carried (Wires.First I M)
abbrev Stop (M E D : τ) := carried (Wires.Second M E D)
abbrev JoinedSignatures (I M E D : τ) :=
  Conditional.Signatures I M M ++ [Threaded (Stop M E D), Threaded (Stop M E D)]

abbrev Producer (Φ : Type u) [HasTy Φ τ] (A I M : τ) :=
  Code (past := []) (Pure τ) (ExplicitRuntime.Effect Φ) (carriedData A) (carriedData (Wires.First I M))
    (.arg (runtimePort (carried A))) (Conditional.Signatures I M M)

abbrev Consumer (Φ : Type u) [HasTy Φ τ] (M E D : τ) :=
  Code (past := []) (Pure τ) (ExplicitRuntime.Effect Φ) (carriedData (Wires.Second M E D)) (carriedData (Wires.Second M E D))
    (.arg (runtimePort (Stop M E D))) [Threaded (Stop M E D)]

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A I M E D : τ) :=
  NestedTheta.Graph (Wires.Op Φ) (Threaded (carried A)) [] (JoinedSignatures I M E D) (Threaded (Stop M E D))

/-- Reuse the existing structural carrier conversion. Its input and output
request the sole live token at the matching boundary. -/
def connector :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData (Wires.First I M)) (carriedData (Wires.Second M E D))
      (.arg (runtimePort (Start I M))) [Threaded (Stop M E D)] :=
  ⟨_, .primitive (.arg (runtimePort (Start I M))) (carriedData _) (carriedData _) (.effect .link)
    (.cons (.arg .head) .nil)
    (.ret (nextRuntime [] (Stop M E D)) (.cons (newest .head []) .nil))⟩

/-- Use the two checked terms, with one explicit carrier conversion. The
splice substitutes the result origins before numbering the outer region. -/
def joinCode (producer : Producer Φ A I M) (consumer : Consumer Φ M E D) :
    Code (past := []) (Pure τ) (Wires.Effect Φ) (carriedData A) (carriedData (Wires.Second M E D))
      (.arg (runtimePort (carried A))) (JoinedSignatures I M E D) :=
  let consumerTail := append (Wires.liftChecked consumer.2).2 (connector (I := I)).2
  append consumerTail.2 (Wires.liftChecked producer.2).2

def join (producer : Producer Φ A I M) (consumer : Consumer Φ M E D) : Graph Φ A I M E D :=
  (joinCode producer consumer).1.toGraph

def joinChecked (producer : Producer Φ A I M) (consumer : Consumer Φ M E D) :
    EntryChecked (a := carriedData A) (b := carriedData (Wires.Second M E D)) (join producer consumer).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (joinCode producer consumer).2

def compile (first : Conditional.Guarded Φ A I B K M M) (second : Loop Φ M C J E D) : Graph Φ A I M E D :=
  join (Conditional.Wiring.code first) (ExplicitRuntime.Wiring.loop second)

abbrev Source (first : Conditional.Guarded Φ A I B K M M) (second : Loop Φ M C J E D) :=
  Flat.link (Flat.Fragment.guarded first) (Flat.Fragment.loop second)

/-- A source-free joint decomposition supplies the two checked local terms,
their existing structural views, and equality of the joint wiring. -/
structure Decomposition (g : Graph Φ A I M E D) (B K C J : τ) where
  producer : Producer Φ A I M
  consumer : Consumer Φ M E D
  first : Conditional.Reverse.Decomposition producer.1.toGraph B K
  second : ExplicitRuntime.Reverse.Decomposition consumer.1.toGraph C J
  wiring : join producer consumer = g

def Decomposition.checked {g : Graph Φ A I M E D} (w : Decomposition g B K C J) :
    EntryChecked (a := carriedData A) (b := carriedData (Wires.Second M E D)) g.toTerm :=
  w.wiring ▸ joinChecked w.producer w.consumer

def Decomposition.recover {g : Graph Φ A I M E D} (w : Decomposition g B K C J) : Fragment Φ A E D :=
  Flat.recover w.first w.second

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered
