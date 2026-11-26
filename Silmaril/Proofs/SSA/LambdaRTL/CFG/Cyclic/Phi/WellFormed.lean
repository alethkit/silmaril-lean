module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.WellFormed.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.GlobalSSA

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.GlobalSSA

universe v w
variable {V K : Type w} {F : Type v} [DecidableEq V] [DecidableEq K]

omit [DecidableEq K] in
private theorem all_contained {names available : List V} :
    names.all (fun name => available.contains name) = true ↔ names ⊆ available := by
  rw [List.all_eq_true]
  exact ⟨fun h _ member => List.contains_iff_mem.mp (h _ member),
    fun h _ member => List.contains_iff_mem.mpr (h member)⟩

omit [DecidableEq V] [DecidableEq K] in
private theorem append_weaken {small large : List V} (le : small ⊆ large) (extra : List V) :
    small ++ extra ⊆ large ++ extra := by
  intro n member
  simp only [List.mem_append] at member ⊢
  exact member.imp (fun h => le h) id

omit [DecidableEq K] in
private theorem scan_append (available : List V) (left right : List (Access V)) :
    Access.scan available (left ++ right) =
      (Access.scan available left).bind (fun seen => Access.scan seen right) := by
  induction left generalizing available with
  | nil => rfl
  | cons front rest ih =>
      cases front with
      | read names =>
          by_cases allowed : names.all (fun n => available.contains n) = true
          · simpa only [List.cons_append, Access.scan, ite_eq_left allowed] using ih available
          · simp only [List.cons_append, Access.scan, ite_eq_right allowed, Option.bind_none]
      | define names => exact ih (available ++ names)

omit [DecidableEq K] in
private theorem scan_weaken {small large seen : List V} {events : List (Access V)}
    (le : small ⊆ large) (ran : Access.scan small events = some seen) :
    Access.scan large events = some (large ++ Access.definitions events) ∧
      seen = small ++ Access.definitions events := by
  induction events generalizing small large with
  | nil =>
      simp [Access.scan] at ran
      subst seen
      simp [Access.scan, Access.definitions]
  | cons front rest ih =>
      cases front with
      | read names =>
          by_cases allowed : names.all (fun n => small.contains n) = true
          · have larger : names.all (fun n => large.contains n) = true :=
              all_contained.mpr (List.Subset.trans (all_contained.mp allowed) le)
            have continued : Access.scan small rest = some seen := by
              simpa only [Access.scan, ite_eq_left allowed] using ran
            simpa only [Access.scan, Access.definitions, ite_eq_left larger] using ih le continued
          · simp only [Access.scan, ite_eq_right allowed] at ran
            cases ran
      | define names =>
          simpa only [Access.scan, Access.definitions, List.append_assoc] using ih (append_weaken le names) ran

omit [DecidableEq K] in
private theorem read_after {inputs seen names : List V} {before after : List (Access V)}
    (ran : Access.scan inputs (before ++ .read names :: after) = some seen) :
    names ⊆ inputs ++ Access.definitions before := by
  rw [scan_append] at ran
  cases first : Access.scan inputs before with
  | none => simp [first] at ran
  | some available =>
      have exactNames := (scan_weaken (List.Subset.refl _) first).2
      by_cases allowed : names.all (fun n => available.contains n) = true
      · rw [← exactNames]
        exact all_contained.mp allowed
      · simp only [first, Option.bind_some, Access.scan, ite_eq_right allowed] at ran
        cases ran

private theorem route_checked {graph : Graph V K F} {inputs : List V} {cert : Certificate V K}
    (checked : check graph inputs cert = true) {source : Option K} {available : List V}
    (arrived : arrival inputs cert source = some available)
    {route : Route V K} (chosen : route ∈ routes graph source) :
    checkRoute cert available route = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at checked
  cases source with
  | none =>
      have same : inputs = available := Option.some.inj arrived
      subst available
      exact checked.2.2.2.1 route chosen
  | some source =>
      change cert.lookup source = some available at arrived
      have member : (source, available) ∈ cert := by
        obtain ⟨before, after, rfl, _⟩ := List.lookup_eq_some_iff.mp arrived
        simp
      exact (checked.2.2.2.2 _ member).2 route chosen

private theorem checkRoute_sound {cert : Certificate V K} {available : List V} {route : Route V K}
    (checked : checkRoute cert available route = true) :
    ∃ seen, Access.scan available route.accesses = some seen ∧
      ∀ target, route.target = some target →
        ∃ required, cert.lookup target = some required ∧ required ⊆ seen := by
  cases h : Access.scan available route.accesses with
  | none => simp [checkRoute, h] at checked
  | some seen =>
      refine ⟨seen, rfl, ?_⟩
      intro target edge
      cases found : cert.lookup target with
      | none => simp [checkRoute, h, edge, found] at checked
      | some required =>
          exact ⟨required, rfl, all_contained.mp (by simpa [checkRoute, h, edge, found] using checked)⟩

private theorem claims_on_path {graph : Graph V K F} {inputs : List V} {cert : Certificate V K}
    (checked : check graph inputs cert = true) {source : Option K} {past : List (Access V)}
    (path : EntryPath graph source past) :
    ∃ required seen, arrival inputs cert source = some required ∧
      Access.scan inputs past = some seen ∧ required ⊆ seen := by
  induction path with
  | entry => exact ⟨inputs, inputs, rfl, rfl, List.Subset.refl _⟩
  | @follow source past route target _ chosen edge ih =>
      obtain ⟨required, seen, arrives, ran, available⟩ := ih
      obtain ⟨expected, scanned, next⟩ := checkRoute_sound (route_checked checked arrives chosen)
      obtain ⟨requiredNext, arrivesNext, carried⟩ := next target edge
      obtain ⟨scannedActual, exactExpected⟩ := scan_weaken available scanned
      refine ⟨requiredNext, seen ++ Access.definitions route.accesses, arrivesNext, ?_, ?_⟩
      · rw [scan_append, ran]
        exact scannedActual
      · rw [exactExpected] at carried
        exact List.Subset.trans carried (append_weaken available _)

theorem check_sound {graph : Graph V K F} {inputs : List V} {cert : Certificate V K}
    (checked : check graph inputs cert = true) : WellFormed graph inputs := by
  have shape := Bool.and_eq_true_iff.mp checked
  refine ⟨shape.1, of_decide_eq_true (Bool.and_eq_true_iff.mp shape.2).1, ?_⟩
  intro source past route path chosen before names after reads
  obtain ⟨required, seen, arrives, ran, available⟩ := claims_on_path checked path
  obtain ⟨_, scanned, _⟩ := checkRoute_sound (route_checked checked arrives chosen)
  have full : Access.scan inputs (past ++ route.accesses) = some (seen ++ Access.definitions route.accesses) := by
    rw [scan_append, ran]
    exact (scan_weaken available scanned).1
  rw [reads] at full
  exact read_after full

theorem compile_sound {graph : Graph V K F} {inputs : List V} {cert : Certificate V K}
    {target : CFG (Option V × Nat) (Option K) F}
    (accepted : GlobalSSA.compile graph inputs cert = some target) :
    WellFormed graph inputs ∧ CFG.Cyclic.Phi.compile graph = some target := by
  by_cases checked : check graph inputs cert = true
  · exact ⟨check_sound checked, by simpa [GlobalSSA.compile, checked] using accepted⟩
  · simp [GlobalSSA.compile, checked] at accepted

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicPhi.GlobalSSA
