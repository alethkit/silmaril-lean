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

private theorem forward_value_reads (storeVersion : Nat) (memory : MemoryInput version)
    (address : Origin args past .address) {latest : Option (Stored args past)}
    {value : Origin args past .word}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (good : Known latest input locals heap)
    (success : forwardValue storeVersion memory address latest = some value) :
    heap.read (readValue address input locals) = readValue value input locals := by
  cases latest with
  | none => cases address <;> simp [forwardValue] at success
  | some stored =>
    cases address with
    | output _ _ => simp [forwardValue] at success
    | arg port =>
      by_cases current : memory.producer.val = storeVersion
      · by_cases same : port.index = stored.address.index
        · have equal : stored.value = value := by
            simpa [forwardValue, current, same] using success
          subst value
          exact port_eq stored.address port same.symm ▸ good
        · simp [forwardValue, current, same] at success
      · simp [forwardValue, current] at success

theorem replaceLoad_denote (memory : MemoryInput version) (address : Origin args past .address)
    (rest : Body args ([.word] :: past) version) (value : Origin args past .word)
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (agrees : heap.read (readValue address input locals) = readValue value input locals) :
    (rewire rest (dropLoad value)).denote input locals heap =
      (Body.load memory address rest).denote input locals heap := by
  simp only [Body.denote, agrees]
  exact rewire_denote rest (dropLoad value) input _ locals heap (drop_reads value input locals)

private theorem forward_load_denote (storeVersion : Nat) (memory : MemoryInput version)
    (address : Origin args past .address) (rest : Body args ([.word] :: past) version)
    {latest : Option (Stored args past)} {rewritten : Body args past version}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (good : Known latest input locals heap)
    (success : forwardLoad storeVersion memory address rest latest = some rewritten) :
    rewritten.denote input locals heap = (Body.load memory address rest).denote input locals heap := by
  obtain ⟨value, matched, rfl⟩ := Option.map_eq_some_iff.mp success
  exact replaceLoad_denote memory address rest value input locals heap
    (forward_value_reads storeVersion memory address input locals heap good matched)

theorem originKey_injective {sort : ValueSort} {x y : Origin args past sort}
    (same : originKey x = originKey y) : x = y := by
  cases x with
  | arg x =>
    cases y with
    | arg y => exact congrArg Origin.arg (port_eq x y (Sum.inl.inj same))
    | output => cases same
  | output i x =>
    cases y with
    | arg => cases same
    | output j y =>
      have keys := Sum.inr.inj same
      have index : i = j := Fin.ext (congrArg Prod.fst keys)
      subst j
      exact congrArg (Origin.output i) (port_eq x y (congrArg Prod.snd keys))

private theorem check_exit_at (storeVersion : Nat) (address : Port args .address)
    (body : Body args past version) {latest : Option (Stored args past)}
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past) (heap : Heap cells)
    (good : Known latest input locals heap)
    (accepted : checkExitAt storeVersion address body latest = true) :
    let result := body.denote input locals heap
    result.2.read (input.get address) = result.1 := by
  induction body generalizing heap with
  | ret memory source =>
    cases matched : forwardValue storeVersion memory (.arg address) latest with
    | none => simp [checkExitAt, matched] at accepted
    | some value =>
      have key : originKey value = originKey source := by
        simpa [checkExitAt, matched] using accepted
      have same := originKey_injective key
      subst source
      exact forward_value_reads storeVersion memory (.arg address) input locals heap good matched
  | load memory target rest ih =>
    exact ih _ _ (known_load good (heap.read (readValue target input locals))) accepted
  | store memory target value rest ih =>
    exact ih _ _ (known_store target value input locals heap) accepted

theorem checkExit_reads (graph : Graph args) (address : Port args .address) (storeVersion : Nat)
    (accepted : checkExit graph address storeVersion = true)
    (input : Tuple (Val cells) args) (heap : Heap cells) :
    let result := graph.denote input heap
    result.2.read (input.get address) = result.1 :=
  check_exit_at storeVersion address graph (latest := none) input PUnit.unit heap trivial accepted

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
