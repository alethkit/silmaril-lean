module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Proofs

open RVSDG (Locals Origin Port Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}
variable {certificate : Certificate args}

private theorem port_eq {sort : ValueSort} (x y : Port args sort) (same : x.index = y.index) :
    x = y := by
  induction x with
  | head => cases y <;> simp_all [Port.index]
  | tail x ih =>
    cases y with
    | head => simp [Port.index] at same
    | tail y => exact congrArg Port.tail (ih y (Nat.succ.inj same))

theorem check_iff_valid (certificate : Certificate args) (input : Tuple (Val cells) args) :
    certificate.check input = true ↔ certificate.Valid input := by
  simp [Certificate.check, Certificate.Valid]

theorem matches_read (address : Origin args past .address)
    (matched : certificate.matches address = true)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) :
    readValue address input locals = cell input certificate.observed := by
  cases address with
  | arg port =>
    have same : port.index = certificate.observed.index := by simpa [Certificate.matches] using matched
    exact congrArg (cell input) (port_eq port certificate.observed same)
  | output => simp [Certificate.matches] at matched

theorem covers_read (address : Origin args past .address)
    (covered : certificate.covers address = true) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (valid : certificate.Valid input) :
    cell input certificate.observed ≠ readValue address input locals := by
  cases address with
  | arg port =>
    obtain ⟨other, member, same⟩ := List.any_eq_true.mp covered
    have equal := port_eq port other (beq_iff_eq.mp same)
    subst other
    exact valid port member
  | output => simp [Certificate.covers] at covered

/-- A retained word reads back from the actual current heap, including
any Stores skipped by the checker. -/
private def Known (certificate : Certificate args) (saved : Option (Origin args past .word))
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) : Prop :=
  match saved with
  | none => True
  | some wire => heap.read (cell input certificate.observed) = readValue wire input locals

private theorem known_load {saved : Option (Origin args past .word)} {input : Tuple (Val cells) args}
    {locals : Locals (Val cells) past} {heap : Heap cells}
    (known : Known certificate saved input locals heap) (word : Word) :
    Known certificate (saved.map raise) input (.cons word .nil, locals) heap := by
  cases saved with
  | none => trivial
  | some wire => cases wire <;> exact known

private theorem known_store (requested published : Nat) (address : Origin args past .address)
    (value : Origin args past .word) (saved : Option (Origin args past .word))
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (valid : certificate.Valid input) (known : Known certificate saved input locals heap) :
    Known certificate (afterStore certificate requested published address value saved) input locals
      (heap.write (readValue address input locals) (readValue value input locals)) := by
  by_cases chosen : published = requested
  · by_cases matched : certificate.matches address = true
    · simp only [afterStore, ite_eq_left chosen, ite_eq_left matched, Known]
      rw [← matches_read address matched input locals]
      exact Heap.read_write_same heap _ _
    · simp [afterStore, chosen, matched, Known]
  · by_cases covered : certificate.covers address = true
    · simp only [afterStore, ite_eq_right chosen, ite_eq_left covered]
      cases saved with
      | none => trivial
      | some producer =>
        exact (Heap.read_write_other heap (readValue address input locals) _
          (readValue value input locals) (covers_read address covered input locals valid)).trans known
    · simp [afterStore, chosen, covered, Known]

private theorem check_exit_at (requested : Nat) (body : Body args past version)
    {saved : Option (Origin args past .word)}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (valid : certificate.Valid input) (known : Known certificate saved input locals heap)
    (accepted : checkExitAt certificate requested body saved = true) :
    let result := body.denote input locals heap
    result.2.read (cell input certificate.observed) = result.1 := by
  induction body generalizing heap with
  | ret memory exported =>
    cases saved with
    | none => simp [checkExitAt] at accepted
    | some value =>
      have key : originKey value = originKey exported := by simpa [checkExitAt] using accepted
      have same := Memory.Forwarding.originKey_injective key
      subst exported
      exact known
  | load memory address rest ih =>
    exact ih _ _ (known_load known (heap.read (readValue address input locals))) accepted
  | @store _ version memory address value rest ih =>
    exact ih _ _ (known_store requested (version + 1) address value _ input locals heap valid known) accepted

theorem checkExitWith_reads (graph : Graph args) (storeVersion : Nat)
    (accepted : checkExitWith graph storeVersion certificate = true)
    (input : Tuple (Val cells) args) (heap : Heap cells) (valid : certificate.Valid input) :
    let result := graph.denote input heap
    result.2.read (cell input certificate.observed) = result.1 :=
  check_exit_at storeVersion graph (saved := none) input PUnit.unit heap valid trivial accepted

private theorem rewrite_at_denote (requested : Nat) (body : Body args past version) (index : Nat)
    {saved : Option (Origin args past .word)} {rewritten : Body args past version}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (valid : certificate.Valid input) (known : Known certificate saved input locals heap)
    (success : rewriteAt certificate requested body index saved = some rewritten) :
    rewritten.denote input locals heap = body.denote input locals heap := by
  induction body generalizing heap index with
  | ret memory value => simp [rewriteAt] at success
  | load memory address rest ih =>
    cases index with
    | zero =>
      by_cases matched : certificate.matches address = true
      · have mapped : saved.map (fun value => rewire rest (dropLoad value)) = some rewritten := by
          simpa [rewriteAt, matched] using success
        obtain ⟨value, eq, rfl⟩ := Option.map_eq_some_iff.mp mapped
        subst saved
        apply Memory.Forwarding.replaceLoad_denote memory address rest value input locals heap
        rw [matches_read address matched input locals]
        exact known
      · simp [rewriteAt, matched] at success
    | succ index =>
      have mapped := Option.map_eq_some_iff.mp
        (show (rewriteAt certificate requested rest index (saved.map raise)).map (.load memory address) =
          some rewritten from success)
      obtain ⟨tail, eq, rfl⟩ := mapped
      let word := heap.read (readValue address input locals)
      exact ih index (.cons word .nil, locals) heap (known_load known word) eq
  | @store _ version memory address value rest ih =>
    cases index with
    | zero => simp [rewriteAt] at success
    | succ index =>
      have mapped := Option.map_eq_some_iff.mp
        (show (rewriteAt certificate requested rest index
          (afterStore certificate requested (version + 1) address value saved)).map (.store memory address value) =
            some rewritten from success)
      obtain ⟨tail, eq, rfl⟩ := mapped
      exact ih index locals _ (known_store requested (version + 1) address value saved input locals heap valid known) eq

theorem rewriteWith_denote {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewriteWith graph candidate certificate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) (valid : certificate.Valid input) :
    rewritten.denote input heap = graph.denote input heap :=
  rewrite_at_denote candidate.storeVersion graph candidate.loadIndex (saved := none)
    input PUnit.unit heap valid trivial success

theorem rewrite_denote {graph rewritten : Graph args} {candidate : Candidate}
    (input : Tuple (Val cells) args) (heap : Heap cells)
    (success : rewrite graph candidate certificate input = some rewritten) :
    rewritten.denote input heap = graph.denote input heap := by
  by_cases checked : certificate.check input = true
  · exact rewriteWith_denote (by simpa [rewrite, checked] using success) input heap
      ((check_iff_valid certificate input).mp checked)
  · simp [rewrite, checked] at success

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Proofs
