module

public import Silmaril.Logic.Institution.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-! Pure equational signatures for regionless operations and operations with isolated
single-block regions. Sorts may be identified by signature maps. -/

@[expose] public section

namespace Silmaril.MLIR.Institution

open CategoryTheory Silmaril.Logic.Institution

/-- The number of block arguments and yielded values of an isolated region. -/
structure RegionArity where
  params : Nat
  yields : Nat

/-- An ordered family of region slots, each with its own parameter and yield counts. -/
structure RegionSlots where
  count : Nat
  slot : Fin count → RegionArity

/-- Slot counts are independent of sorts. A regionless operation has no region slots. -/
structure OpArity (withRegions : Bool) where
  operands : Nat
  results : Nat
  regions : if withRegions then RegionSlots else Unit

/-- The ordered region slots of an operation. -/
abbrev OpArity.regionArities : {withRegions : Bool} → OpArity withRegions → RegionSlots
  | false, _ => ⟨0, Fin.elim0⟩
  | true, a => a.regions

abbrev OpArity.Region {withRegions : Bool} (a : OpArity withRegions) := Fin a.regionArities.count

abbrev OpArity.region {withRegions : Bool} (a : OpArity withRegions) (r : a.Region) : RegionArity :=
  a.regionArities.slot r

/-- Ordered sorts for operands, results, block arguments and yields. -/
structure Profile {withRegions : Bool} (a : OpArity withRegions) (Ty : Type) where
  operand : Fin a.operands → Ty
  result : Fin a.results → Ty
  param : (r : a.Region) → Fin (a.region r).params → Ty
  yield : (r : a.Region) → Fin (a.region r).yields → Ty

def Profile.map {withRegions : Bool} {a : OpArity withRegions} {Ty Ty' : Type}
    (f : Ty → Ty') (p : Profile a Ty) : Profile a Ty' where
  operand i := f (p.operand i)
  result i := f (p.result i)
  param r i := f (p.param r i)
  yield r i := f (p.yield r i)

/-- A signature of symbols indexed by their full typed operation profile. -/
structure Signature (withRegions : Bool) where
  Ty : Type
  Op : {a : OpArity withRegions} → Profile a Ty → Type

/-- Maps may identify sorts and symbols. Every operand, result, block parameter and yield
retains its slot and has its sort mapped by `sort`. -/
structure Signature.Hom {withRegions : Bool} (S T : Signature withRegions) where
  sort : S.Ty → T.Ty
  symbol : ∀ {a : OpArity withRegions} {p : Profile a S.Ty}, S.Op p → T.Op (p.map sort)

instance {withRegions : Bool} : Category (Signature withRegions) where
  Hom := Signature.Hom
  id _ := ⟨id, id⟩
  comp f g := ⟨g.sort ∘ f.sort, fun o => g.symbol (f.symbol o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Assign a value to each position of a typed context, including the empty context. -/
abbrev Assignment {Ty : Type} (carrier : Ty → Type) {n : Nat} (Γ : Fin n → Ty) :=
  (i : Fin n) → carrier (Γ i)

/-- A pure expression. An application selects one result of an operation. Each region body
is a tuple of expressions in exactly its block-parameter context. -/
inductive Term {withRegions : Bool} (S : Signature withRegions) :
    {n : Nat} → (Fin n → S.Ty) → S.Ty → Type
  | var {n : Nat} {Γ : Fin n → S.Ty} (i : Fin n) : Term S Γ (Γ i)
  | app {n : Nat} {Γ : Fin n → S.Ty} {a : OpArity withRegions} {p : Profile a S.Ty} (op : S.Op p)
      (args : (i : Fin a.operands) → Term S Γ (p.operand i))
      (bodies : (r : a.Region) → (i : Fin (a.region r).yields) → Term S (p.param r) (p.yield r i))
      (result : Fin a.results) : Term S Γ (p.result result)

/-- Single-block syntax in expression form, with a common input context and ordered yields. -/
abbrev Block {withRegions : Bool} (S : Signature withRegions) {n m : Nat}
    (Γ : Fin n → S.Ty) (Δ : Fin m → S.Ty) :=
  (i : Fin m) → Term S Γ (Δ i)

variable {withRegions : Bool} {S T : Signature withRegions}

/-- Rename symbols and reindex sorts throughout the term, including inside region bodies. -/
def Term.map (f : S ⟶ T) {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty} :
    Term S Γ s → Term T (f.sort ∘ Γ) (f.sort s)
  | .var i => .var i
  | .app o args bodies i =>
      .app (f.symbol o) (fun j => (args j).map f) (fun r j => (bodies r j).map f) i

/-- Substitute for the outer input positions. Isolated region bodies have their own inputs. -/
def Term.subst {n m : Nat} {Γ : Fin n → S.Ty} {Δ : Fin m → S.Ty} {s : S.Ty}
    (σ : Block S Δ Γ) : Term S Γ s → Term S Δ s
  | .var i => σ i
  | .app o args bodies i => .app o (fun j => (args j).subst σ) bodies i

/-- Total set-valued semantics. A region argument is a function from parameter assignments to
assignments of yielded values and can be used by the interpretation of its enclosing operation. -/
structure Model (S : Signature withRegions) where
  carrier : S.Ty → Type
  op : ∀ {a : OpArity withRegions} {p : Profile a S.Ty}, S.Op p →
    Assignment carrier p.operand →
    ((r : a.Region) → Assignment carrier (p.param r) → Assignment carrier (p.yield r)) →
    Assignment carrier p.result

/-- Pull carriers and operations back along a typed symbol map. -/
def Model.reduct (f : S ⟶ T) (M : Model T) : Model S where
  carrier := M.carrier ∘ f.sort
  op o := M.op (f.symbol o)

/-- Evaluate a term. Each isolated body receives a fresh parameter assignment supplied by the
operation's interpretation. -/
def Term.denote (M : Model S) {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty} :
    Term S Γ s → Assignment M.carrier Γ → M.carrier s
  | .var i, env => env i
  | .app o args bodies i, env =>
      M.op o (fun j => (args j).denote M env)
        (fun r params j => (bodies r j).denote M params) i

/-- An equation between two blocks of the same type, universally quantified over inputs. -/
structure Equation (S : Signature withRegions) where
  inputs : Nat
  outputs : Nat
  context : Fin inputs → S.Ty
  results : Fin outputs → S.Ty
  lhs : Block S context results
  rhs : Block S context results

def Equation.map (f : S ⟶ T) (e : Equation S) : Equation T where
  inputs := e.inputs
  outputs := e.outputs
  context := f.sort ∘ e.context
  results := f.sort ∘ e.results
  lhs i := (e.lhs i).map f
  rhs i := (e.rhs i).map f

def Equation.Holds (M : Model S) (e : Equation S) : Prop :=
  ∀ env : Assignment M.carrier e.context, ∀ i, (e.lhs i).denote M env = (e.rhs i).denote M env

/-- This institution uses discrete model categories. -/
def room (S : Signature withRegions) : Room.{0, 1, 1} where
  Sen := Equation S
  Mod := Cat.of (Discrete (Model S))
  Sat M := Equation.Holds M.as

def reductFunctor (f : S ⟶ T) : Discrete (Model T) ⥤ Discrete (Model S) :=
  Discrete.functor (fun M => Discrete.mk (M.reduct f))

end Silmaril.MLIR.Institution
