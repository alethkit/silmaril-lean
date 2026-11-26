module

public import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Proofs

open RVSDG (Locals Origin Port Tuple)

variable {args : List ValueSort} {past target : List (List ValueSort)}
variable {version cells : Nat}

private theorem port_eq {sort : ValueSort} (x y : Port args sort) (same : x.index = y.index) :
    x = y := by
  induction x with
  | head => cases y <;> simp_all [Port.index]
  | tail x ih =>
    cases y with
    | head => simp [Port.index] at same
    | tail y => exact congrArg Port.tail (ih y (Nat.succ.inj same))

private theorem read_raise {sort : ValueSort} (wire : Origin args past sort)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (word : Word) :
    readValue (raise wire) input (.cons word .nil, locals) = readValue wire input locals := by
  cases wire <;> rfl

private abbrev Reads (route : Routing args past target) (input : Tuple (Val cells) args)
    (old : Locals (Val cells) past) (new : Locals (Val cells) target) :=
  ∀ {s} (wire : Origin args past s), readValue (route wire) input new = readValue wire input old

private theorem under_reads {route : Routing args past target} {input : Tuple (Val cells) args}
    {old : Locals (Val cells) past} {new : Locals (Val cells) target}
    (reads : Reads route input old new) (word : Word) :
    Reads route.underLoad input (.cons word .nil, old) (.cons word .nil, new) := by
  intro s wire
  cases wire with
  | arg p => exact (read_raise (route (.arg p)) input new word).trans (reads (.arg p))
  | output i p =>
    refine Fin.cases (motive := fun j => ∀ q : Port ([.word] :: past)[j] s,
      readValue (route.underLoad (.output j q)) input
          (.cons (t := ValueSort.word) word .nil, new) =
        readValue (.output (past := [.word] :: past) j q) input
          (.cons (t := ValueSort.word) word .nil, old)) ?_ ?_ i p
    · intro q
      rfl
    · intro j q
      exact (read_raise (route (.output j q)) input new word).trans (reads (.output j q))

private theorem drop_reads (value : Origin args past .word) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) :
    Reads (dropLoad value) input (.cons (readValue value input locals) .nil, locals) locals := by
  intro s wire
  cases wire with
  | arg p => rfl
  | output i p =>
    refine Fin.cases (motive := fun j => ∀ q : Port ([.word] :: past)[j] s,
      readValue (dropLoad value (.output j q)) input locals =
        readValue (.output (past := [.word] :: past) j q) input
          (.cons (t := ValueSort.word) (readValue value input locals) .nil, locals)) ?_ ?_ i p
    · intro q
      cases q with
      | head => rfl
      | tail p => exact nomatch p
    · intro j q
      rfl

private theorem rewire_denote (body : Body args past version) (route : Routing args past target)
    (input : Tuple (Val cells) args) (old : Locals (Val cells) past)
    (new : Locals (Val cells) target) (heap : Heap cells) (reads : Reads route input old new) :
    (rewire body route).denote input new heap = body.denote input old heap := by
  induction body generalizing target heap with
  | ret memory value => simp only [rewire, Body.denote, reads]
  | load memory address rest ih =>
    simp only [rewire, Body.denote, reads]
    apply ih
    exact under_reads reads _
  | store memory address value rest ih =>
    simp only [rewire, Body.denote, reads]
    exact ih route old new _ reads

/-- The remembered Store supplies the selected cell of the live heap. -/
private def Known (latest : Option (Stored args past)) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (heap : Heap cells) : Prop :=
  match latest with
  | none => True
  | some stored => heap.read (input.get stored.address) = readValue stored.value input locals

private theorem known_store (address : Origin args past .address) (value : Origin args past .word)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells) :
    Known (Stored.ofStore address value) input locals
      (heap.write (readValue address input locals) (readValue value input locals)) := by
  cases address with
  | arg port => exact Heap.read_write_same heap (input.get port) (readValue value input locals)
  | output _ _ => trivial

private theorem known_load {latest : Option (Stored args past)} {input : Tuple (Val cells) args}
    {locals : Locals (Val cells) past} {heap : Heap cells} (good : Known latest input locals heap)
    (word : Word) : Known (latest.map Stored.underLoad) input (.cons word .nil, locals) heap := by
  cases latest with
  | none => trivial
  | some stored => simpa only [Option.map_some, Known, Stored.underLoad, read_raise] using good

private theorem forward_load_denote (storeVersion : Nat) (memory : MemoryInput version)
    (address : Origin args past .address) (rest : Body args ([.word] :: past) version)
    {latest : Option (Stored args past)} {rewritten : Body args past version}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (good : Known latest input locals heap)
    (success : forwardLoad storeVersion memory address rest latest = some rewritten) :
    rewritten.denote input locals heap = (Body.load memory address rest).denote input locals heap := by
  cases latest with
  | none => cases address <;> simp [forwardLoad] at success
  | some stored =>
    cases address with
    | output _ _ => simp [forwardLoad] at success
    | arg port =>
      by_cases current : memory.producer.val = storeVersion
      · by_cases same : port.index = stored.address.index
        · have equal : rewire rest (dropLoad stored.value) = rewritten := by
            simpa [forwardLoad, current, same] using success
          subst rewritten
          have read : heap.read (input.get port) = readValue stored.value input locals :=
            port_eq stored.address port same.symm ▸ good
          change (rewire rest (dropLoad stored.value)).denote input locals heap =
            rest.denote input (.cons (heap.read (input.get port)) .nil, locals) heap
          rw [read]
          exact rewire_denote rest (dropLoad stored.value) input _ locals heap
            (drop_reads stored.value input locals)
        · simp [forwardLoad, current, same] at success
      · simp [forwardLoad, current] at success

private theorem rewrite_at_denote (storeVersion : Nat) (body : Body args past version) (index : Nat)
    {latest : Option (Stored args past)} {rewritten : Body args past version}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (good : Known latest input locals heap)
    (success : rewriteAt storeVersion body index latest = some rewritten) :
    rewritten.denote input locals heap = body.denote input locals heap := by
  induction body generalizing index heap with
  | ret memory value => simp [rewriteAt] at success
  | load memory address rest ih =>
    cases index with
    | zero => exact forward_load_denote storeVersion memory address rest input locals heap good success
    | succ index =>
      have mapped := Option.map_eq_some_iff.mp
        (show (rewriteAt storeVersion rest index (latest.map Stored.underLoad)).map
          (.load memory address) = some rewritten from success)
      obtain ⟨tail, eq, rfl⟩ := mapped
      let word := heap.read (readValue address input locals)
      exact ih index (.cons word .nil, locals) heap (known_load good word) eq
  | store memory address value rest ih =>
    cases index with
    | zero => simp [rewriteAt] at success
    | succ index =>
      have mapped := Option.map_eq_some_iff.mp
        (show (rewriteAt storeVersion rest index (Stored.ofStore address value)).map
          (.store memory address value) = some rewritten from success)
      obtain ⟨tail, eq, rfl⟩ := mapped
      exact ih index locals _ (known_store address value input locals heap) eq

theorem rewrite_denote {graph rewritten : Graph args} {candidate : Candidate}
    (success : rewrite graph candidate = some rewritten)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    rewritten.denote input heap = graph.denote input heap :=
  rewrite_at_denote candidate.storeVersion graph candidate.loadIndex (latest := none)
    input PUnit.unit heap trivial success

end Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Proofs
