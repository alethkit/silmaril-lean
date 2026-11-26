module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Proofs

open RVSDG (Locals Origin Port Tuple)
open Memory.Forwarding (originKey_injective)
open Memory.Forwarding.Disjoint (Certificate cell)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}
variable {facts : Certificate args}

theorem reindexMemory_denote (body : Body args past version) (live : Nat)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    (reindexMemory body live).denote input locals heap = body.denote input locals heap := by
  induction body generalizing live heap with
  | ret => rfl
  | load _ _ _ ih => exact ih _ _ _
  | store _ _ _ _ ih => exact ih _ _ _

private theorem arg_read (port other : Port args .address) (same : port.index = other.index)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) :
    readValue (.arg port) input locals = cell input other := by
  have wire : (Origin.arg port : Origin args past .address) = .arg other :=
    originKey_injective (congrArg Sum.inl same)
  exact congrArg (fun address => readValue address input locals) wire

private theorem matches_read (address : Origin args past .address) (matched : facts.matches address = true)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) :
    readValue address input locals = cell input facts.observed := by
  cases address with
  | arg port => exact arg_read port _ (beq_iff_eq.mp matched) input locals
  | output => cases matched

private theorem covers_read (address : Origin args past .address) (covered : facts.covers address = true)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input) :
    cell input facts.observed ≠ readValue address input locals := by
  cases address with
  | arg port =>
    obtain ⟨other, listed, same⟩ := List.any_eq_true.mp covered
    rw [arg_read port other (beq_iff_eq.mp same) input locals]
    exact valid other listed
  | output => cases covered

private def AgreeOutside (observed : Address cells) (first second : Heap cells) : Prop :=
  ∀ other, other ≠ observed → first.read other = second.read other

private theorem writes_agree {observed written : Address cells} {first second : Heap cells}
    (agrees : AgreeOutside observed first second) (word : Word) :
    AgreeOutside observed (first.write written word) (second.write written word) := by
  intro other distinct
  by_cases same : other = written
  · subst other
    simp only [Heap.read_write_same]
  · simpa only [Heap.read_write_other _ _ _ _ same] using agrees other distinct

private theorem overwrite_agrees {observed : Address cells} {first second : Heap cells}
    (agrees : AgreeOutside observed first second) (word : Word) :
    first.write observed word = second.write observed word := by
  funext other
  change (first.write observed word).read other = (second.write observed word).read other
  by_cases same : other = observed
  · subst other
    simp only [Heap.read_write_same]
  · exact writes_agree agrees word other same

private theorem noReadUntil_denote (overwrite : Nat) (body : Body args past version)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input)
    (first second : Heap cells) (agrees : AgreeOutside (cell input facts.observed) first second)
    (checked : noReadUntil facts overwrite body = true) :
    body.denote input locals first = body.denote input locals second := by
  induction body generalizing first second with
  | ret => cases checked
  | load _ address _ ih =>
    obtain ⟨reader, rest⟩ := Bool.and_eq_true_iff.mp checked
    have disjoint := covers_read address (Bool.and_eq_true_iff.mp reader).2 input locals valid
    have same := agrees (readValue address input locals) disjoint.symm
    simp only [Body.denote, same]
    exact ih _ _ _ agrees rest
  | @store _ version _ address value _ ih =>
    by_cases hit : version + 1 = overwrite
    · have matched : facts.matches address = true := by
        simpa only [noReadUntil, ite_eq_left hit] using checked
      simp only [Body.denote, matches_read address matched input locals]
      rw [overwrite_agrees agrees (readValue value input locals)]
    · have rest := show noReadUntil facts overwrite _ = true by
        simpa only [noReadUntil, ite_eq_right hit] using checked
      exact ih _ _ _ (writes_agree agrees (readValue value input locals)) rest

private theorem rewriteAt_denote (candidate : Candidate) (body rewritten : Body args past version)
    (success : rewriteAt candidate facts body = some rewritten)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (valid : facts.Valid input)
    (heap : Heap cells) :
    rewritten.denote input locals heap = body.denote input locals heap := by
  induction body generalizing heap with
  | ret => cases success
  | load _ _ _ ih =>
    obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
    exact ih tail accepted _ _
  | @store _ version _ address value rest ih =>
    by_cases hit : version + 1 = candidate.removeVersion
    · simp only [rewriteAt, ite_eq_left hit] at success
      split at success
      next checked =>
        have same := Option.some.inj success
        subst rewritten
        obtain ⟨matched, safe⟩ := Bool.and_eq_true_iff.mp checked
        have outside : AgreeOutside (cell input facts.observed) heap
            (heap.write (readValue address input locals) (readValue value input locals)) := by
          intro other distinct
          rw [matches_read address matched input locals]
          exact (Heap.read_write_other heap _ _ _ distinct).symm
        exact (reindexMemory_denote rest version input locals heap).trans
          (noReadUntil_denote candidate.overwriteVersion rest input locals valid _ _ outside safe)
      next => cases success
    · simp only [rewriteAt, ite_eq_right hit] at success
      obtain ⟨tail, accepted, rfl⟩ := Option.map_eq_some_iff.mp success
      exact ih tail accepted _ _

theorem rewriteWith_denote {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewriteWith graph candidate facts = some rewritten)
    (input : Tuple (Val cells) args) (valid : facts.Valid input) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  rewriteAt_denote candidate graph rewritten success input PUnit.unit valid heap

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Proofs
