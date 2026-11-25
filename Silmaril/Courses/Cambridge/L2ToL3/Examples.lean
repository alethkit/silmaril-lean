module

import Silmaril.Courses.Cambridge.L2ToL3.Thms
import Silmaril.Courses.Cambridge.L2ToL3.Bytes

open Silmaril.Courses.Cambridge
open L2ToL3 AstCodec

private def counter : L2.Expr :=
  .letRecFun .int .int (.seq (.assign "λ" (.bvar 0)) (.deref "λ")) (.app (.bvar 0) (.int 7))

private def initial : L2.Store := L1.Store.empty.insert "λ" 1
private def final : L2.Store := initial.insert "λ" 7
private def ctx : L2.TypeEnv :=
  { L2.TypeEnv.empty with locs := (∅ : L1.TypeEnv).insert "λ" .intref }

private theorem counter_typed : L2.HasType ctx counter .int :=
  .letRecFun
    (.seq (.assign (by simp [ctx, L2.TypeEnv.push]) (.bvar rfl))
      (.deref (by simp [ctx, L2.TypeEnv.push])))
    (.app (.bvar rfl) (.int 7))

private theorem counter_run : L2.Steps ⟨counter, initial⟩ ⟨.int 7, final⟩ :=
  .head .letRecFun <|
    .head (.appFun (.int 7)) <|
    .head .letRecFun <|
    .head (.seqStep (.assignValue (n := 7) (by simp [initial]))) <|
    .head .seqSkip (.single (.deref (by simp)))

example : L3.OperationalInstitution.semantics.May (config unicodeLayout ⟨counter, initial⟩)
    (.returned (config unicodeLayout ⟨.int 7, final⟩)) := by
  exact (may_return_iff unicodeLayout counter_typed).2
    ((L2.OperationalInstitution.may_return_iff _ _).2 ⟨counter_run, .int 7⟩)

-- An untyped L2 Boolean write is stuck, while its L3 image can store that Boolean.
example : L2.Stuck ⟨.assign "λ" (.bool true), initial⟩ := by
  refine ⟨(fun value => ?_), fun _ move => ?_⟩
  · cases value
  · cases move with
    | assignStep inside => cases inside

example : ∃ next, L3.Step (config unicodeLayout ⟨.assign "λ" (.bool true), initial⟩) next :=
  ⟨_, .assignValue ⟨.bool true, .bool true⟩ ((mem_store unicodeLayout _ _).2 (by simp [initial]))⟩

-- An identically spelled variable and location have different syntactic roles.
example : targetTree unicodeLayout (.assign "λ" (.fvar "λ")) =
    envelope "L3" "resolved-term"
      (node "assign" [node "loc" [.atom (unicodeLayout "λ").repr], node "fvar" [.atom "λ"]]) := rfl

example :
    (sexpBytes unicodeLayout ((SExpBytes.codec L2.ResolvedCodec.termSExp).encode counter) >>=
      (SExpBytes.codec L3.ResolvedCodec.termSExp).decode?) =
      some (expr unicodeLayout counter) := by
  rw [sexpBytes_encode]
  exact SExpBytes.decode_encode _ _
