module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Proofs

open RVSDG (Origin Port Tuple)
open Memory.Forwarding (originKey_injective)

variable {args : List ValueSort} {cells : Nat}
variable {source : Loop.Graph args} {result : Result args}

private theorem select_spec {observed : Port args .address} {sites : List (StoreSite args)}
    {version : Nat} {writers : List (Port args .address)}
    (success : select observed sites = some (version, writers)) :
    ∃ newer older, sites = newer ++ (version, some observed) :: older ∧
      newer.map Prod.snd = writers.map some ∧
      ∀ writer ∈ writers, writer.index ≠ observed.index := by
  induction sites generalizing version writers with
  | nil => simp [select] at success
  | cons site rest ih =>
    obtain ⟨published, address⟩ := site
    cases address with
    | none => simp [select] at success
    | some writer =>
      by_cases same : writer.index = observed.index
      · have wire : (Origin.arg writer : Origin args [] .address) = .arg observed :=
          originKey_injective (congrArg Sum.inl same)
        have equal := Origin.arg.inj wire
        simp only [select, ite_eq_left same, Option.some.injEq, Prod.mk.injEq] at success
        obtain ⟨rfl, rfl⟩ := success
        exact ⟨[], rest, by simp [equal], rfl, by simp⟩
      · simp only [select, ite_eq_right same] at success
        obtain ⟨⟨selected, later⟩, chosen, returned⟩ := Option.map_eq_some_iff.mp success
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj returned
        obtain ⟨newer, older, order, coverage, different⟩ := ih chosen
        refine ⟨(published, some writer) :: newer, older, ?_, ?_, ?_⟩
        · rw [List.cons_append, order]
        · simp only [List.map_cons, coverage]
        · intro port member
          rcases List.mem_cons.mp member with rfl | member
          · exact same
          · exact different port member

private theorem rewriteWith_storeVersion {target : Graph args} {version : Nat}
    {facts : Memory.Forwarding.Disjoint.Certificate args}
    (success : Carried.rewriteWith source version facts = some target) :
    target.storeVersion = version := by
  cases bodyEq : source.body with
  | ret => simp [Carried.rewriteWith, bodyEq] at success
  | store => simp [Carried.rewriteWith, bodyEq] at success
  | load =>
    simp only [Carried.rewriteWith, bodyEq] at success
    split at success
    next => exact (congrArg Graph.storeVersion (Option.some.inj success)).symm
    next => cases success

theorem discover_spec (success : discover source = some result) :
    Carried.rewriteWith source result.graph.storeVersion result.facts = some result.graph ∧
      capturedAddress source = some result.facts.observed ∧
      ∃ newer older,
        (stores source.body).reverse =
          newer ++ (result.graph.storeVersion, some result.facts.observed) :: older ∧
        newer.map Prod.snd = result.facts.writers.map some ∧
        ∀ writer ∈ result.facts.writers, writer.index ≠ result.facts.observed.index := by
  obtain ⟨observed, captured, scanned⟩ := Option.bind_eq_some_iff.mp success
  obtain ⟨⟨chosen, writers⟩, found, checked⟩ := Option.bind_eq_some_iff.mp scanned
  obtain ⟨target, accepted, returned⟩ := Option.bind_eq_some_iff.mp checked
  cases Option.some.inj returned
  have version := rewriteWith_storeVersion accepted
  exact ⟨by simpa only [version] using accepted, captured, by simpa only [version] using select_spec found⟩

theorem discoverChecked_eq_some_iff (input : Tuple (Val cells) args) :
    discoverChecked source input = some result ↔
      discover source = some result ∧ result.facts.Valid input := by
  constructor
  · intro success
    obtain ⟨candidate, found, checked⟩ := Option.bind_eq_some_iff.mp success
    split at checked
    next valid =>
      have same := Option.some.inj checked
      subst candidate
      exact ⟨found, (result.facts.check_iff_valid input).mp valid⟩
    next => cases checked
  · rintro ⟨found, valid⟩
    simp [discoverChecked, found, (result.facts.check_iff_valid input).mpr valid]

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Search.Proofs
