module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Functions.Defs
public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Thms
import Silmaril.Proofs.Logic.Temporal.TLA.Data.Tagged.Graphs

public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

namespace Graph

theorem pairs_injective : Function.Injective Graph.pairs.{u} := by
  intro a b h
  cases a; cases b; cases h; rfl

variable {g h : Graph.{u}} {x y : Value.{u}}

theorem mem_domain : g.domain.mem x ↔ ∃ y, g.relates x y :=
  Proofs.mem_domain

theorem lookup_eq_some : g.lookup x = some y ↔ g.relates x y :=
  Proofs.lookup_eq_some

theorem lookup_eq_none : g.lookup x = none ↔ ¬ g.domain.mem x :=
  Proofs.lookup_eq_none

theorem ext (hh : ∀ x, g.lookup x = h.lookup x) : g = h :=
  Proofs.graph_eq_of_relates fun x y => by rw [← lookup_eq_some, hh, lookup_eq_some]

theorem ext_of_domain_lookup (hd : g.domain = h.domain)
    (he : ∀ x, g.domain.mem x → g.lookup x = h.lookup x) : g = h :=
  Proofs.ext_of_domain_lookup hd he

theorem relates_ofFn {s : SetData.{u}} {f : Value.{u} → Value.{u}} :
    (ofFn s f).relates x y ↔ s.mem x ∧ f x = y :=
  Proofs.relates_ofFn

@[simp] theorem domain_ofFn (s : SetData.{u}) (f : Value.{u} → Value.{u}) :
    (ofFn s f).domain = s :=
  Proofs.domain_ofFn s f

theorem lookup_ofFn {s : SetData.{u}} {f : Value.{u} → Value.{u}} (hx : s.mem x) :
    (ofFn s f).lookup x = some (f x) :=
  Proofs.lookup_ofFn hx

theorem update_missing (hx : ¬ g.domain.mem x) : g.update x y = g :=
  Proofs.update_missing hx

@[simp] theorem domain_update (g : Graph.{u}) (x y : Value.{u}) : (g.update x y).domain = g.domain :=
  Proofs.domain_update g x y

theorem lookup_update (hx : g.domain.mem x) : (g.update x y).lookup x = some y := by
  classical
  simp only [update, hx, ite_true]
  simpa using lookup_ofFn (f := fun k => if k = x then y else (g.lookup k).getD y) hx

theorem lookup_update_other {k : Value.{u}} (hne : k ≠ x) :
    (g.update x y).lookup k = g.lookup k :=
  Proofs.lookup_update_other hne

end Graph

theorem SetData.mem_functionSet {s t : SetData.{u}} {v : Value.{u}} :
    (s.functionSet t).mem v ↔ ∃ g : Graph.{u}, Value.function g = v ∧ g.domain = s ∧
      ∀ x y, g.relates x y → t.mem y :=
  Proofs.mem_functionSet

namespace Value

theorem function_injective : Function.Injective (function.{u}) :=
  fun _ _ h => Graph.pairs_injective (tagged_inj.mp h).2

theorem function_ne_set (g : Graph.{u}) (s : SetData.{u}) : function g ≠ set s :=
  fun h => Kind.noConfusion (tagged_inj.mp h).1

theorem asFunction_eq_some {v : Value.{u}} {g : Graph.{u}} :
    v.asFunction = some g ↔ function g = v :=
  decode_eq_some function_injective

@[simp] theorem asFunction_function (g : Graph.{u}) : (function g).asFunction = some g :=
  asFunction_eq_some.mpr rfl

@[simp] theorem asFunction_set (s : SetData.{u}) : (set s).asFunction = none :=
  decode_eq_none (fun ⟨g, h⟩ => function_ne_set g s h)

@[simp] theorem asSet_function (g : Graph.{u}) : (function g).asSet = none :=
  decode_eq_none (fun ⟨s, h⟩ => function_ne_set g s h.symm)

variable (policy : Unspecified.{u}) {g : Graph.{u}} {f x y : Value.{u}}

@[simp] theorem domain_function (g : Graph.{u}) : domain policy (function g) = set g.domain := by
  simp [domain]

theorem domain_nonfunction (h : f.asFunction = none) : domain policy f = policy .domain [f] := by
  simp [domain, h]

theorem apply_function (h : g.relates x y) : apply policy (function g) x = y := by
  simp [apply, Graph.lookup_eq_some.mpr h]

theorem apply_missing (h : ¬ g.domain.mem x) :
    apply policy (function g) x = policy .apply [function g, x] := by
  simp [apply, Graph.lookup_eq_none.mpr h]

theorem apply_nonfunction (h : f.asFunction = none) : apply policy f x = policy .apply [f, x] := by
  simp [apply, h]

@[simp] theorem update_function (g : Graph.{u}) (x y : Value.{u}) :
    update policy (function g) x y = function (g.update x y) := by
  simp [update]

theorem update_missing (h : ¬ g.domain.mem x) : update policy (function g) x y = function g := by
  rw [update_function, Graph.update_missing h]

theorem update_nonfunction (h : f.asFunction = none) :
    update policy f x y = policy .update [f, x, y] := by
  simp [update, h]

end Value

end Silmaril.Logic.Temporal.TLA.Data.Tagged
