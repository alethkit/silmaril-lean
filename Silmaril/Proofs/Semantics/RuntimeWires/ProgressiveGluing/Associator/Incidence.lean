module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Associator.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Associator.Rename

public section

namespace Silmaril.RuntimeWires.Proofs.CollarAssociator

open ProgressiveGraph

universe u v
variable {O : Type u} {S : Signature.{u,v} O} {L M R A B C : ℕ}
variable {d : ProgressiveGraph.Diagram S L A .point} {e : ProgressiveGraph.Diagram S M B .point}
variable {f : ProgressiveGraph.Diagram S R C .point}

@[expose] def vertexEquiv (L M R : ℕ) : Fin ((L + M) + R) ≃ Fin (L + (M + R)) where
  toFun := Fin.cast (Nat.add_assoc ..)
  invFun := Fin.cast (Nat.add_assoc ..).symm
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

theorem vertex_A (a : Fin L) :
    vertexEquiv L M R (Fin.castAdd R (Fin.castAdd M a)) = Fin.castAdd (M + R) a :=
  Fin.ext rfl

theorem vertex_B (b : Fin M) :
    vertexEquiv L M R (Fin.castAdd R (Fin.natAdd L b)) = Fin.natAdd L (Fin.castAdd R b) :=
  Fin.ext rfl

theorem vertex_C (c : Fin R) :
    vertexEquiv L M R (Fin.natAdd (L + M) c) = Fin.natAdd L (Fin.natAdd M c) :=
  Fin.ext (Nat.add_assoc ..)

theorem vertex_cases (v : Fin ((L + M) + R)) :
    (∃ a : Fin L, Fin.castAdd R (Fin.castAdd M a) = v) ∨
    (∃ b : Fin M, Fin.castAdd R (Fin.natAdd L b) = v) ∨
    (∃ c : Fin R, Fin.natAdd (L + M) c = v) := by
  induction v using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => exact .inl ⟨a, rfl⟩
    | right b => exact .inr (.inl ⟨b, rfl⟩)
  | right c => exact .inr (.inr ⟨c, rfl⟩)

theorem generator_lower (m : d.OrderedVerticalMatch e) (j : Fin L) :
    m.glue.generator (Fin.castAdd M j) = d.generator j := by
  rw [sameGlue m, m.upperJoin.glue_generator_lower]
  exact m.lowerJoin.glue_generator_lower j

theorem generator_upper (m : d.OrderedVerticalMatch e) (j : Fin M) :
    m.glue.generator (Fin.natAdd L j) = e.generator j := by
  rw [sameGlue m]
  exact m.upperJoin.glue_generator_upper j

theorem inputs_lower (m : d.OrderedVerticalMatch e) (j : Fin L) :
    m.glue.inputs (Fin.castAdd M j) = (d.inputs j).map (leftWire m) := by
  rw [sameGlue m, m.upperJoin.glue_inputs_lower]
  change (m.lowerJoin.glue.inputs (Fin.castAdd 0 j)).map _ = _
  rw [m.lowerJoin.glue_inputs_lower, List.map_map]
  rfl

theorem inputs_upper (m : d.OrderedVerticalMatch e) (j : Fin M) :
    m.glue.inputs (Fin.natAdd L j) = (e.inputs j).map (rightWire m) := by
  rw [sameGlue m]
  exact m.upperJoin.glue_inputs_upper j

theorem outputs_lower (m : d.OrderedVerticalMatch e) (j : Fin L) :
    m.glue.outputs (Fin.castAdd M j) = (d.outputs j).map (leftWire m) := by
  rw [sameGlue m, m.upperJoin.glue_outputs_lower]
  change (m.lowerJoin.glue.outputs (Fin.castAdd 0 j)).map _ = _
  rw [m.lowerJoin.glue_outputs_lower, List.map_map]
  rfl

theorem outputs_upper (m : d.OrderedVerticalMatch e) (j : Fin M) :
    m.glue.outputs (Fin.natAdd L j) = (e.outputs j).map (rightWire m) := by
  rw [sameGlue m]
  exact m.upperJoin.glue_outputs_upper j

variable (m : d.OrderedVerticalMatch e) (n : e.OrderedVerticalMatch f)

theorem assoc_generator (j : Fin ((L + M) + R)) :
    (before m n).glue.generator (vertexEquiv L M R j) = (after m n).glue.generator j := by
  rcases vertex_cases j with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
  · rw [vertex_A, generator_lower, generator_lower, generator_lower]
  · rw [vertex_B, generator_upper, generator_lower, generator_lower, generator_upper]
  · rw [vertex_C, generator_upper, generator_upper, generator_upper]

theorem assoc_label (w : LeftWires m n) :
    (before m n).glue.label (wireEquiv m n w) = (after m n).glue.label w := by
  change (before m n).glue.label (toRight m n w) = _
  rcases left_cases m n w with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
  · rw [toRight_A]; unfold leftA rightA; rw [left_label, left_label, left_label]
  · rw [toRight_B]; unfold leftB rightB; rw [right_label, left_label, left_label, right_label]
  · rw [toRight_C]; unfold leftC rightC; rw [right_label, right_label, right_label]

theorem assoc_ports
    (ports : ∀ {V W}, ProgressiveGraph.Diagram S V W .point → Fin V → List (Fin W))
    (lo : ∀ {V W A B} {a : ProgressiveGraph.Diagram S V A .point}
      {b : ProgressiveGraph.Diagram S W B .point} (p : a.OrderedVerticalMatch b) (i : Fin V),
      ports p.glue (Fin.castAdd W i) = (ports a i).map (leftWire p))
    (hi : ∀ {V W A B} {a : ProgressiveGraph.Diagram S V A .point}
      {b : ProgressiveGraph.Diagram S W B .point} (p : a.OrderedVerticalMatch b) (i : Fin W),
      ports p.glue (Fin.natAdd V i) = (ports b i).map (rightWire p))
    (j : Fin ((L + M) + R)) :
    ports (before m n).glue (vertexEquiv L M R j) = (ports (after m n).glue j).map (wireEquiv m n) := by
  change _ = (ports (after m n).glue j).map (toRight m n)
  rcases vertex_cases j with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨c, rfl⟩
  · rw [vertex_A, lo, lo, lo, List.map_map, List.map_map]
    exact congrArg (fun k => (ports d a).map k) (funext fun a => (toRight_A m n a).symm)
  · rw [vertex_B, hi, lo, lo, hi, List.map_map, List.map_map, List.map_map]
    exact congrArg (fun k => (ports e b).map k) (funext fun b => (toRight_B m n b).symm)
  · rw [vertex_C, hi, hi, hi, List.map_map, List.map_map]
    exact congrArg (fun k => (ports f c).map k) (funext fun c => (toRight_C m n c).symm)

@[expose] noncomputable def assocIncidence : (after m n).glue.IncidenceEquiv (before m n).glue where
  vertex := vertexEquiv L M R
  wire := wireEquiv m n
  generator := assoc_generator m n
  label := assoc_label m n
  inputs := assoc_ports m n (fun d => d.inputs) inputs_lower inputs_upper
  outputs := assoc_ports m n (fun d => d.outputs) outputs_lower outputs_upper

/-- The ordered port equations also determine the boundary endpoints. -/
theorem endpoints_map {V W V' W' : Type*} (vertices : V ≃ V') (wires : W ≃ W')
    (source : W → Option V) (target : W' → Option V')
    (ports : V → List W) (ports' : V' → List W')
    (source_exact : ∀ w v, source w = some v ↔ w ∈ ports v)
    (target_exact : ∀ w v, target w = some v ↔ w ∈ ports' v)
    (port_eq : ∀ j, ports' (vertices j) = (ports j).map wires) (w : W) :
    target (wires w) = (source w).map vertices := by
  have atEach (j : V) : target (wires w) = some (vertices j) ↔ source w = some j := by
    rw [target_exact, source_exact, port_eq, List.mem_map]
    exact ⟨fun ⟨i, hi, he⟩ => wires.injective he ▸ hi, fun h => ⟨w, h, rfl⟩⟩
  cases eq : source w with
  | some j => exact (atEach j).mpr eq
  | none =>
    cases he : target (wires w) with
    | none => rfl
    | some j =>
      obtain ⟨i, rfl⟩ := vertices.surjective j
      have impossible : (none : Option V) = some i := eq.symm.trans ((atEach i).mp he)
      cases impossible

section Endpoints

variable {V W V' W' : ℕ}
variable {a : ProgressiveGraph.Diagram S V W .point} {b : ProgressiveGraph.Diagram S V' W' .point}

theorem incidence_start (p : a.IncidenceEquiv b) (w : Fin W) :
    b.start (p.wire w) = (a.start w).map p.vertex :=
  endpoints_map p.vertex p.wire a.start b.start a.outputs b.outputs
    (fun w j => (a.output_exact j w).trans List.mem_ofFn.symm)
    (fun w j => (b.output_exact j w).trans List.mem_ofFn.symm) p.outputs w

theorem incidence_finish (p : a.IncidenceEquiv b) (w : Fin W) :
    b.finish (p.wire w) = (a.finish w).map p.vertex :=
  endpoints_map p.vertex p.wire a.finish b.finish a.inputs b.inputs
    (fun w j => (a.input_exact j w).trans List.mem_ofFn.symm)
    (fun w j => (b.input_exact j w).trans List.mem_ofFn.symm) p.inputs w

end Endpoints
end Silmaril.RuntimeWires.Proofs.CollarAssociator
