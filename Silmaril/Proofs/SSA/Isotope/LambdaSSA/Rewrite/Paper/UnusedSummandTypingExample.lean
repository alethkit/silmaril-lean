module

import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Trim.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnaryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Coherence.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms

/-! # Two live labels with heterogeneous common payloads -/

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.UnusedSummandFixture

open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical Semantics.Categorical.UnusedSummand
open Extension.Singleton Extension.Singleton.StructuralValues

private inductive Op where
  | poll

private abbrev U : Ty Empty := Silmaril.unit
private abbrev Flag : Ty Empty := Silmaril.coprod U U

instance : HasTy Op (Ty Empty) where
  src _ := U
  trg _ := Flag

instance : HasEff Op Bool := ⟨fun _ => true⟩

private def payloads : Fin 2 → Ty Empty := Fin.cases U (fun _ => Flag)
private def emptyLeft : Fin 2 → Ty Empty := Fin.cases .empty (fun _ => U)
private def emptyRight : Fin 2 → Ty Empty := Fin.cases U (fun _ => .empty)

private def first : Row (Φ := Op) payloads [U] [Flag] :=
  .case (.op .poll .unit)
    (.jump 1 (.var 1 rfl))
    (.exit 0 rfl (.var 0 rfl))

private def second : Row (Φ := Op) payloads [U] [Flag] := .jump 0 .unit

private def table : Program (Φ := Op) payloads [U] [Flag] where
  entry := .jump 0 .unit
  blocks := Fin.cases first (fun _ => second)

/-- The selected poll reply either transfers to the second label with the
retained flag, or returns the reply. The second label transfers back. -/
example :
    table.region true =
      .cfg (.br 0 (.inl .unit)) 2
        (Fin.cases (.case (.op .poll .unit)
          (.br 1 (.inl (.var 2))) (.br 2 (.var 0)))
          (fun _ => .br 0 (.inl .unit))) := by
  unfold Program.region table
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

example : (table.region true).HasType [Flag] [U] := table.hasType (some emptyLeft)
example : (table.region true).HasType [Flag] [U] := table.hasType (some emptyRight)

private theorem covers : table.targetsEveryLabel := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .inl rfl
  · obtain rfl := Fin.eq_zero j
    exact .inr ⟨0, .inl rfl⟩

private def sparse : Program (Φ := Op) payloads [U] [Flag] where
  entry := .jump 0 .unit
  blocks _ := .exit 0 rfl .unit

/-- An untargeted label can have a type outside the widened family. -/
private def sparseFamily : Fin 2 → Ty Empty := Fin.cases (Silmaril.coprod U .empty) (fun _ => U)

private theorem sparseFamily_outside (D : Fin 2 → Ty Empty) :
    sparseFamily ≠ family payloads (some D) := by
  intro eq
  have chosen := congrFun eq (1 : Fin 2)
  change Ty.unit = Ty.coprod Flag (D 1) at chosen
  cases chosen

private theorem sparse_not_covered : ¬ sparse.targetsEveryLabel := by
  intro coverage
  rcases coverage 1 with h | ⟨_, h⟩
  · have neq : (0 : Fin 2) ≠ 1 := by decide
    exact neq h
  · exact False.elim h

local notation "Seed" => WithCaseReturns.BinaryFold.JoinedStep (τ := Ty Empty) (Φ := Op) true
local notation "inc" => inclusion Seed
local notation "model" => typeModel Seed

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive guardedIteration guardedElgot
attribute [local instance] Extension.Singleton.StructuralValues.hasFiniteCoproducts

private theorem chosenRolling : IterationRolling (Extension.Singleton.TypeCategory Seed) :=
  fun h step => iterateChosen_roll Seed h step

/-- These are exact graph witnesses for two distinct widened families of the
same raw CFG, and for its common-family rendering. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∃ f, RegionDenotes inc model (table.hasType none) f ∧
      RegionDenotes inc model (table.hasType (some emptyLeft)) f ∧
      RegionDenotes inc model (table.hasType (some emptyRight)) f := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  obtain ⟨f, agrees⟩ := table.denotes_agree inc model chosenRolling
  exact ⟨f, agrees none, agrees (some emptyLeft), agrees (some emptyRight)⟩

/-- The two-label comparison consumes independently quantified exact graph
witnesses, with no family supplied to the proof by the caller. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f g}, RegionDenotes inc model (table.hasType (some emptyLeft)) f →
      RegionDenotes inc model (table.hasType (some emptyRight)) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f g d e
  exact table.denotes_eq inc model chosenRolling covers d e

/-- The same top-level inversion also compares a widened witness with an
arbitrary witness of the common rendering. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f g}, RegionDenotes inc model (table.hasType (some emptyLeft)) f →
      RegionDenotes inc model (table.hasType none) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f g d e
  exact table.denotes_eq inc model chosenRolling covers d e

/-- The graph really admits an internal family outside the widened shape
when label 1 has no written incoming jump. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ¬ sparse.targetsEveryLabel ∧
    ∃ f : (inc).obj (ctxObj model [Flag]) ⟶ (inc).obj (labelObj model [U]),
      CfgDenotesAt inc model sparseFamily (sparse.entry.region true id)
        (fun i => (sparse.blocks i).region true Nat.succ) f ∧
      ∀ D, sparseFamily ≠ family payloads (some D) := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  have he : (sparse.entry.region true id).HasType [Flag] (List.ofFn sparseFamily ++ [U]) :=
    .br rfl (.inl .unit)
  have hb (i : Fin 2) :
      ((sparse.blocks i).region true Nat.succ).HasType (sparseFamily i :: [Flag])
        (List.ofFn sparseFamily ++ [U]) := .br rfl .unit
  obtain ⟨f, w⟩ := CfgDenotesAt.exists_of_typing inc model sparseFamily he hb
  exact ⟨sparse_not_covered, f, w, sparseFamily_outside⟩

/-- The two exact witnesses disagree on the type of untargeted label 1.
The conclusion holds for independently supplied entry and row denotations. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f g},
      CfgDenotesAt inc model sparseFamily (sparse.entry.region true id)
        (fun i => (sparse.blocks i).region true Nat.succ) f →
      sparse.denotesAt inc model (some emptyRight) g →
      f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f g d e
  exact sparse.denotes_eq_trimmed inc model chosenRolling
    (d.denotes inc model (t := sparse.hasType (some emptyLeft)))
    (e.denotes inc model (t := sparse.hasType (some emptyRight)))

private def noTargets : Program (Φ := Op) payloads [U, U] [Flag] where
  entry := .case (.op .poll .unit) (.exit 0 rfl .unit) (.exit 1 rfl .unit)
  blocks _ := .exit 1 rfl .unit

/-- In the empty residual case the effectful entry still selects its
original ordered outward label. -/
example (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    (∀ i, ¬ noTargets.targets i) ∧
      ∀ {f g}, RegionDenotes inc model (noTargets.hasType none) f →
        RegionDenotes inc model (noTargets.hasType (some emptyRight)) g → f = g := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  refine ⟨?_, fun d e => noTargets.denotes_eq_trimmed inc model chosenRolling d e⟩
  intro i target
  rcases target with (h | h) | ⟨_, h⟩ <;> exact h

section NativeLet

private def initializer : Operand (Φ := Op) [Flag] U := .let₁ .unit (.var 0 rfl)

private def letEntry : Region Op :=
  .let₁ (.let₁ .unit (.var 0)) (.br 0 (.inl (.var 0)))

private def letBlocks : Fin 2 → Region Op :=
  Fin.cases
    (.let₁ (.op .poll .unit)
      (.case (.var 0) (.br 0 (.inl (.var 0))) (.br 3 (.var 0))))
    (fun _ => .let₁ .unit (.br 2 (.var 0)))

private def letProgram : Program (Φ := Op) payloads [U, U] [Flag] where
  entry := .let₁ initializer (.jump 0 (.var 0 rfl))
  blocks := Fin.cases
    (.let₁ (.op .poll .unit) (.case (.var 0 rfl)
      (.jump 0 (.var 0 rfl)) (.exit 1 rfl (.var 0 rfl))))
    (fun _ => .let₁ .unit (.exit 0 rfl (.var 0 rfl)))

private theorem letProgram_region : letProgram.region true = .cfg letEntry 2 letBlocks := by
  unfold Program.region letProgram letEntry letBlocks
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private def letFamily (tail spare : Ty Empty) : Fin 2 → Ty Empty :=
  Fin.cases (Silmaril.coprod U tail) (fun _ => spare)

private theorem letEntry_typed (tail spare : Ty Empty) :
    letEntry.HasType [Flag] (List.ofFn (letFamily tail spare) ++ [U, U]) :=
  .let₁ (.let₁ .unit (.var rfl)) (.br rfl (.inl (.var rfl)))

private theorem letBlocks_typed (tail spare : Ty Empty) (i : Fin 2) :
    (letBlocks i).HasType (letFamily tail spare i :: [Flag])
      (List.ofFn (letFamily tail spare) ++ [U, U]) := by
  refine Fin.cases ?_ (fun _ => ?_) i
  · exact .let₁ (.op .unit) (.case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl)))
  · exact .let₁ .unit (.br rfl (.var rfl))

private theorem letFamily_distinct : letFamily .empty U ≠ letFamily U .empty := by
  intro eq
  have spare := congrFun eq (1 : Fin 2)
  change Ty.unit = Ty.empty at spare
  cases spare

private theorem untargeted : ¬ letProgram.targets 1 := by
  intro hit
  rcases hit with h | ⟨i, h⟩
  · have neq : (0 : Fin 2) ≠ 1 := by decide
    exact neq h
  · revert h
    refine Fin.cases ?_ (fun _ h => h) i
    rintro (h | h)
    · have neq : (0 : Fin 2) ≠ 1 := by decide
      exact neq h
    · exact h

variable {V C : Type} [Category V] [Category C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : Silmaril.Isotope.LetIter.Semantics.Categorical.TypeModel (Ty Empty) V)
  [Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel J M Op]

/-- The entry uses a native term let. Its exact witnesses agree at the
synthesized type, including the type of the term binder. -/
example {t : Tm.HasType [Flag] (.let₁ (.unit : Tm Op) (.var 0)) U}
    {f g : J.obj (ctxObj M [Flag]) ⟶ J.obj (M.obj U)}
    (d : Denotes J M t f) (e : Denotes J M t g) : f = g :=
  (initializer.determined (Ren.id _)).denotes_eq J M d e

example :
    (∃ f : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U]),
      CfgDenotesAt J M (letFamily .empty U) letEntry letBlocks f) ∧
    (∃ g : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U]),
      CfgDenotesAt J M (letFamily U .empty) letEntry letBlocks g) :=
  ⟨CfgDenotesAt.exists_of_typing J M _ (letEntry_typed .empty U) (letBlocks_typed .empty U),
   CfgDenotesAt.exists_of_typing J M _ (letEntry_typed U .empty) (letBlocks_typed U .empty)⟩

/-- Two independently typed witnesses of the raw CFG compare. The poll is
bound once; its reply selects a repeat or the second outward index. The
untargeted block uses the first outward index and has different parameter
types in the two graph witnesses. -/
example (roll : IterationRolling C) :
    (¬ letProgram.targets 1) ∧ (letFamily .empty U ≠ letFamily U .empty) ∧
    ∀ {f g : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U])},
      CfgDenotesAt J M (letFamily .empty U) letEntry letBlocks f →
      CfgDenotesAt J M (letFamily U .empty) letEntry letBlocks g → f = g := by
  refine ⟨untargeted, letFamily_distinct, ?_⟩
  intro f g d e
  have asRendered {tail spare : Ty Empty} {h}
      (w : CfgDenotesAt J M (letFamily tail spare) letEntry letBlocks h) :
      ∃ t : (letProgram.region true).HasType [Flag] [U, U], RegionDenotes J M t h := by
    rw [letProgram_region]
    exact ⟨.cfg _ (letEntry_typed tail spare) (letBlocks_typed tail spare), w.denotes J M⟩
  obtain ⟨_, left⟩ := asRendered d
  obtain ⟨_, right⟩ := asRendered e
  exact letProgram.denotes_eq_trimmed J M roll left right

/-- The final label context does not select an intermediate type for a raw
unannotated initializer. Even a body that branches on the bound value can
admit both typings. -/
private def ambiguousLet : Region Op :=
  .let₁ (.inl .unit) (.case (.var 0) (.br 0 .unit) (.br 1 .unit))

private theorem ambiguousLet_typed (tail : Ty Empty) : ambiguousLet.HasType [Flag] [U, U] :=
  Region.HasType.let₁ (A := Silmaril.coprod U tail) (.inl .unit)
    (.case (.var rfl) (.br rfl .unit) (.br rfl .unit))

example : ambiguousLet.HasType [Flag] [U, U] ∧
    ¬ ∃ A : Ty Empty, TypeDetermined [Flag] (.inl (.unit : Tm Op)) A := by
  refine ⟨ambiguousLet_typed U, ?_⟩
  rintro ⟨A, determined⟩
  have left := determined (Silmaril.coprod U U) (.inl .unit)
  have right := determined (Silmaril.coprod U (Ty.empty : Ty Empty)) (.inl .unit)
  have eq := (Ty.coprod.inj (left.trans right.symm)).2
  cases eq

/-- The ambiguity checked above still permits agreement of all exact
witnesses of that particular raw let. -/
example {f g : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U])}
    (d : RegionDenotes J M (ambiguousLet_typed U) f)
    (e : RegionDenotes J M (ambiguousLet_typed .empty) g) : f = g := by
  have fixed : TypeDetermined [Flag] (.unit : Tm Op) U := by
    intro D h
    cases h
    rfl
  exact RegionDenotes.let_inl_case_eq J M fixed .unit
    (left := .br 0 .unit) (right := .br 1 .unit) (right' := .br 1 .unit) (.br rfl .unit) d e

private def pollPayload : Operand (Φ := Op) [Flag] Flag := .op .poll .unit

private def selectedArm : Region Op :=
  .case (.var 0) (.br 0 (.inl (.var 0))) (.br 3 (.var 0))

private def unselectedArm : Region Op :=
  .case (.var 1) (.br 3 .unit) (.br 2 .unit)

private def taggedEntry : Region Op :=
  .let₁ (.inl pollPayload.term)
    (.case (.var 0) (selectedArm.renameVars (Silmaril.DeBruijn.lift Nat.succ)) unselectedArm)

private def taggedBlocks : Fin 2 → Region Op :=
  Fin.cases (.br 2 .unit) (fun _ => .br 3 .unit)

private def payloadProgram : Program (Φ := Op) payloads [U, U] [Flag] where
  entry := .let₁ pollPayload
    (.case (.var 0 rfl) (.jump 0 (.var 0 rfl)) (.exit 1 rfl (.var 0 rfl)))
  blocks := Fin.cases (.exit 0 rfl .unit) (fun _ => .exit 1 rfl .unit)

private theorem payloadProgram_region :
    payloadProgram.region true = .cfg (.let₁ pollPayload.term selectedArm) 2 taggedBlocks := by
  unfold Program.region payloadProgram taggedBlocks
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem payloadProgram_sparse : ¬ payloadProgram.targets 1 := by
  rintro ((hit | hit) | ⟨i, hit⟩)
  · have neq : (0 : Fin 2) ≠ 1 := by decide
    exact neq hit
  · exact hit
  · revert hit
    exact Fin.cases (fun h => h) (fun _ h => h) i

/-- The sum binder's type is selected explicitly when assembling each entry
witness. The untaken arm even cases on that sum a second time. -/
private theorem taggedEntry_graph (tail spare other : Ty Empty) :
    ∃ (he : taggedEntry.HasType [Flag] (List.ofFn (letFamily tail spare) ++ [U, U]))
      (f : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M (List.ofFn (letFamily tail spare) ++ [U, U]))),
      RegionDenotes J M he f := by
  let S := Silmaril.coprod Flag other
  have hl : (selectedArm.renameVars (Silmaril.DeBruijn.lift Nat.succ)).HasType
      (Flag :: S :: [Flag]) (List.ofFn (letFamily tail spare) ++ [U, U]) :=
    .case (.var rfl) (.br rfl (.inl (.var rfl))) (.br rfl (.var rfl))
  have hr : unselectedArm.HasType (other :: S :: [Flag])
      (List.ofFn (letFamily tail spare) ++ [U, U]) :=
    .case (.var rfl) (.br rfl .unit) (.br rfl .unit)
  have hp : pollPayload.term.HasType [Flag] Flag := .op .unit
  exact ⟨_, _, RegionDenotes.let₁ (Denotes.inl (B := other) (denote_spec J M hp))
    (RegionDenotes.case (.var rfl) (denoteRegion_spec J M hl) (denoteRegion_spec J M hr))⟩

private theorem taggedCfg_graph (tail spare other : Ty Empty) :
    ∃ f : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U]),
      CfgDenotesAt J M (letFamily tail spare) taggedEntry taggedBlocks f := by
  obtain ⟨he, fe, de⟩ := taggedEntry_graph J M tail spare other
  have hb (i : Fin 2) : (taggedBlocks i).HasType (letFamily tail spare i :: [Flag])
      (List.ofFn (letFamily tail spare) ++ [U, U]) :=
    Fin.cases (.br rfl .unit) (fun _ => .br rfl .unit) i
  obtain ⟨joint, dj⟩ := collectiveDenotes_exists_succ J M 1 [Flag]
    (letFamily tail spare) [U, U] (fun i => denoteRegion J M (hb i))
  exact ⟨_, he, hb, fe, _, joint, de, (fun i => denoteRegion_spec J M (hb i)), dj, rfl⟩

example :
    (∃ f : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U]),
      CfgDenotesAt J M (letFamily .empty U) taggedEntry taggedBlocks f) ∧
    (∃ g : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U]),
      CfgDenotesAt J M (letFamily U .empty) taggedEntry taggedBlocks g) :=
  ⟨taggedCfg_graph J M .empty U U, taggedCfg_graph J M U .empty .empty⟩

/-- From arbitrary exact witnesses, preserve the actual sparse CFG output.
The single poll decides between local label 0 (then outward index 0) and
outward index 1. No live transfer targets internal label 1. -/
example (roll : IterationRolling C) :
    (¬ payloadProgram.targets 1) ∧
    ∀ {f g : J.obj (ctxObj M [Flag]) ⟶ J.obj (labelObj M [U, U])},
      CfgDenotesAt J M (letFamily .empty U) taggedEntry taggedBlocks f →
      CfgDenotesAt J M (letFamily U .empty) taggedEntry taggedBlocks g → f = g := by
  refine ⟨payloadProgram_sparse, ?_⟩
  intro f g d e
  have determined : TypeDetermined [Flag] pollPayload.term Flag :=
    pollPayload.typeDetermined (Ren.id _)
  obtain ⟨he, hb, _, _, _, de, db, dc, rfl⟩ := d
  obtain ⟨he', hb', _, _, _, de', db', dc', rfl⟩ := e
  exact payloadProgram.denotes_eq_let_inl_case_entry J M roll determined payloadProgram_region
    (RegionDenotes.cfg he hb de db dc) (RegionDenotes.cfg he' hb' de' db' dc')

end NativeLet

end Silmaril.Isotope.LambdaSSA.Region.Paper.UnusedSummandFixture
