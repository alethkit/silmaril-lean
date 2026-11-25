module

public import Silmaril.Logic.Temporal.TLA.Data.Tagged.Defs

/-! # Mathematical functions on tagged TLA+ values -/

@[expose] public section

namespace Silmaril.Logic.Temporal.TLA.Data.Tagged

universe u

/-- A set of internal ordered pairs with at most one output for each input. -/
structure Graph where
  pairs : ZFSet.{u}
  pair_form : ∀ p ∈ pairs, ∃ x y, ZFSet.pair x y = p
  single_valued : ∀ {x y z}, ZFSet.pair x y ∈ pairs → ZFSet.pair x z ∈ pairs → y = z

def Value.function (g : Graph.{u}) : Value.{u} := .tagged .function g.pairs

noncomputable def Value.asFunction : Value.{u} → Option Graph.{u} :=
  decode Value.function

namespace Graph

def relates (g : Graph.{u}) (x y : Value.{u}) : Prop :=
  ZFSet.pair x.code y.code ∈ g.pairs

/-- Each key belongs to the double union of the graph, using Kuratowski pairs. -/
def domain (g : Graph.{u}) : SetData.{u} :=
  ⟨g.pairs.sUnion.sUnion.sep (fun x => ∃ y, g.relates ⟨x⟩ y)⟩

noncomputable def lookup (g : Graph.{u}) (x : Value.{u}) : Option Value.{u} :=
  open Classical in
  if h : ∃ y, g.relates x y then some (Classical.choose h) else none

/-- Form the graph from a mathematical domain and a value expression on it. -/
noncomputable def ofFn (s : SetData.{u}) (f : Value.{u} → Value.{u}) : Graph.{u} where
  pairs := ZFSet.range (fun x : s.codes => ZFSet.pair x.val (f ⟨x.val⟩).code)
  pair_form := fun _ h =>
    let ⟨x, hx⟩ := ZFSet.mem_range.mp h
    ⟨x.val, (f ⟨x.val⟩).code, hx⟩
  single_valued := by
    intro x y z hy hz
    simp only [ZFSet.mem_range, ZFSet.pair_inj] at hy hz
    obtain ⟨⟨a, _⟩, rfl, rfl⟩ := hy
    obtain ⟨⟨b, _⟩, rfl, rfl⟩ := hz
    rfl

/-- Replace an existing component. A key outside the domain leaves the graph unchanged. -/
noncomputable def update (g : Graph.{u}) (x y : Value.{u}) : Graph.{u} :=
  open Classical in
  if g.domain.mem x then
    ofFn g.domain (fun k => if k = x then y else (g.lookup k).getD y)
  else g

end Graph

/-- The set of all graphs with the indicated domain and range bound. -/
noncomputable def SetData.functionSet (s t : SetData.{u}) : SetData.{u} :=
  ⟨ZFSet.range (fun g : ZFSet.funs s.codes t.codes => (Value.tagged .function g.val).code)⟩

namespace Value

noncomputable def domain (policy : Unspecified.{u}) (f : Value.{u}) : Value.{u} :=
  match f.asFunction with
  | some g => set g.domain
  | none => policy .domain [f]

noncomputable def apply (policy : Unspecified.{u}) (f x : Value.{u}) : Value.{u} :=
  ((f.asFunction).bind (fun g => g.lookup x)).getD (policy .apply [f, x])

noncomputable def update (policy : Unspecified.{u}) (f x y : Value.{u}) : Value.{u} :=
  match f.asFunction with
  | some g => function (g.update x y)
  | none => policy .update [f, x, y]

end Value

end Silmaril.Logic.Temporal.TLA.Data.Tagged
