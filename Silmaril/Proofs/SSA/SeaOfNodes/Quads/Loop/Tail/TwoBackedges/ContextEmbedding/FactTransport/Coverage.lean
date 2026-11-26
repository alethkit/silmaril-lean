module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition.Thms

/-! Successful typed intersections are uniquely determined by their coverage. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Semantics.Dataflow (Flat)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)
open Blocks (Bank)
open Identification (BankMap pushFacts pull)
open SCCP.Dispatch.DeleteRoute.Bypass.Backends.Guarded.Institution (EntryFacts)

variable {old middle new : List (ValueSort Width)}

private theorem distinct_values (sort : ValueSort Width) :
    ∃ a b : sortValue Word sort, a ≠ b := by
  cases sort with
  | predicate => exact ⟨⟨false⟩, ⟨true⟩, by intro equal; cases equal⟩
  | data width =>
    refine ⟨(0 : Word width), (1 : Word width), ?_⟩
    intro equal
    have below : 1 < 2 ^ width.val := Nat.one_lt_pow (Nat.ne_of_gt width.property) (by decide)
    have digits := congrArg BitVec.toNat equal
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt below] at digits

private theorem covers_cons {sort : ValueSort Width} (head : Fact Word (.value sort))
    (tail : EntryFacts old) (value : sortValue Word sort) (rest : Bank (regs := old) model) :
    TupleCovers (Tuple.cons head tail) (Tuple.cons value rest) ↔ head.Covers value ∧ TupleCovers tail rest :=
  ⟨fun h => ⟨h .head, fun p => h (.tail p)⟩, fun h _ p => match p with
    | .head => h.1
    | .tail port => h.2 port⟩

theorem covered_of_nonbottom (facts : EntryFacts old)
    (cells : ∀ t (p : RVSDG.Port (dataPorts old) t), facts.get p ≠ .bottom) :
    ∃ input : Bank (regs := old) model, TupleCovers facts input := by
  induction old with
  | nil =>
    cases facts
    exact ⟨.nil, fun port => nomatch port⟩
  | cons sort rest ih =>
    cases facts with
    | cons head tail =>
      obtain ⟨input, cover⟩ := ih tail (fun t p => cells t (.tail p))
      have defined : head ≠ .bottom := cells _ .head
      cases head with
      | bottom => exact (defined rfl).elim
      | constant value =>
        exact ⟨.cons value input, (covers_cons (.constant value) tail value input).mpr ⟨rfl, cover⟩⟩
      | overdefined =>
        obtain ⟨value, _, _⟩ := distinct_values sort
        exact ⟨.cons value input, (covers_cons .overdefined tail value input).mpr ⟨True.intro, cover⟩⟩

private theorem flat_eq_of_cover {α : Type} (left right : Flat α)
    (distinct : ∃ x y : α, x ≠ y) (witness : α) (l : left.Covers witness) (r : right.Covers witness)
    (same : ∀ x, left.Covers x ↔ right.Covers x) : left = right := by
  cases left with
  | bottom => exact l.elim
  | overdefined =>
    cases right with
    | bottom => exact r.elim
    | overdefined => rfl
    | constant value =>
      obtain ⟨x, y, different⟩ := distinct
      exact (different (((same x).mp True.intro).symm.trans ((same y).mp True.intro))).elim
  | constant value =>
    cases right with
    | bottom => exact r.elim
    | overdefined =>
      obtain ⟨x, y, different⟩ := distinct
      exact (different (((same x).mpr True.intro).symm.trans ((same y).mpr True.intro))).elim
    | constant other => exact congrArg Flat.constant (l.trans r.symm)

/-- A nonempty Cartesian product of the supported flat coordinates has a unique fact tuple. -/
private theorem facts_eq_of_coverage (left right : EntryFacts old) (witness : Bank (regs := old) model)
    (covered : TupleCovers left witness)
    (same : ∀ input : Bank (regs := old) model, TupleCovers left input ↔ TupleCovers right input) :
    left = right := by
  induction old with
  | nil => cases left; cases right; rfl
  | cons sort rest ih =>
    cases left with
    | cons leftHead leftTail =>
      cases right with
      | cons rightHead rightTail =>
        cases witness with
        | cons value tail =>
          have leftCover := (covers_cons _ _ _ _).mp covered
          have rightCover := (covers_cons _ _ _ _).mp ((same (.cons value tail)).mp covered)
          have headSame (x : sortValue Word sort) : leftHead.Covers x ↔ rightHead.Covers x := by
            have coveredAt := (covers_cons leftHead leftTail x tail).symm.trans
              ((same (.cons x tail)).trans (covers_cons rightHead rightTail x tail))
            exact ⟨fun h => (coveredAt.mp ⟨h, leftCover.2⟩).1, fun h => (coveredAt.mpr ⟨h, rightCover.2⟩).1⟩
          have tailSame (input : Bank (regs := rest) model) :
              TupleCovers leftTail input ↔ TupleCovers rightTail input := by
            have coveredAt := (covers_cons leftHead leftTail value input).symm.trans
              ((same (.cons value input)).trans (covers_cons rightHead rightTail value input))
            exact ⟨fun h => (coveredAt.mp ⟨leftCover.1, h⟩).2, fun h => (coveredAt.mpr ⟨rightCover.1, h⟩).2⟩
          exact congrArg₂ Tuple.cons (flat_eq_of_cover _ _ (distinct_values sort) _ leftCover.1 rightCover.1 headSame)
            (ih leftTail rightTail tail leftCover.2 tailSame)

theorem pushFacts_has_cover (map : BankMap old new) (facts : EntryFacts old) (out : EntryFacts new)
    (pushed : pushFacts map facts = some out) : ∃ input : Bank (regs := new) model, TupleCovers out input :=
  covered_of_nonbottom out fun _ port => Identification.pushFacts_nonbottom map facts out pushed port

private theorem option_eq_of_coverage (left right : Option (EntryFacts new))
    (leftNonempty : ∀ facts, left = some facts → ∃ input : Bank (regs := new) model, TupleCovers facts input)
    (rightNonempty : ∀ facts, right = some facts → ∃ input : Bank (regs := new) model, TupleCovers facts input)
    (same : ∀ input : Bank (regs := new) model,
      (∃ f, left = some f ∧ TupleCovers f input) ↔ (∃ f, right = some f ∧ TupleCovers f input)) :
    left = right := by
  cases left with
  | none =>
    cases right with
    | none => rfl
    | some facts =>
      obtain ⟨input, cover⟩ := rightNonempty facts rfl
      obtain ⟨_, impossible, _⟩ := (same input).mpr ⟨facts, rfl, cover⟩
      cases impossible
  | some facts =>
    obtain ⟨input, cover⟩ := leftNonempty facts rfl
    cases right with
    | none =>
      obtain ⟨_, impossible, _⟩ := (same input).mp ⟨facts, rfl, cover⟩
      cases impossible
    | some other =>
      exact congrArg some (facts_eq_of_coverage facts other input cover fun valuation => by
        simpa using same valuation)

theorem pushFacts_comp (first : BankMap old middle) (second : BankMap middle new) (facts : EntryFacts old) :
    pushFacts (Composition.thenMap first second) facts =
      (pushFacts first facts).bind (pushFacts second) := by
  apply option_eq_of_coverage
  · exact pushFacts_has_cover _ _
  · intro out staged
    obtain ⟨mid, _, pushed⟩ := Option.bind_eq_some_iff.mp staged
    exact pushFacts_has_cover second mid out pushed
  · intro input
    refine (Composition.pushFacts_thenMap first second facts input).trans ?_
    constructor
    · rintro ⟨mid, out, firstOk, secondOk, covered⟩
      exact ⟨out, Option.bind_eq_some_iff.mpr ⟨mid, firstOk, secondOk⟩, covered⟩
    · rintro ⟨out, staged, covered⟩
      obtain ⟨mid, firstOk, secondOk⟩ := Option.bind_eq_some_iff.mp staged
      exact ⟨mid, out, firstOk, secondOk, covered⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Proofs
