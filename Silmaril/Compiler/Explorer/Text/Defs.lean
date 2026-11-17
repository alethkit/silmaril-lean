module

public import Silmaril.Compiler.Explorer.Defs

/-!
# Text-file problems: the primary form, with or without semantics

The explorer's primary problem is about **files**: some source files, some target files, and a
relation between them. Nothing here requires a semantics.

* `Files`: an immutable map from file names to bytes (the database content-addresses each file).
* `IncludeEnv`: what a C preprocessor reads besides the main file: the files it may include,
  the search order, the predefined macros and the compiler options. A formal preprocessor would
  be a `Stage` from `(IncludeEnv × Files)` to the preprocessed text; none exists yet.
* `Stage α β`: one step of a pipeline (parse, preprocess, elaborate, disassemble, lower), a
  partial function with a name and a trust tag. A stage's exact output is an artifact the
  explorer shows next to its input; a trusted stage is later replaced by a verified one or by a
  translation-validation problem of its own (`Stage.validated`).
* `RelProblem α β`: an arbitrary relation between a source and a target. It may have no
  semantics at all (`Semantics.none`): "gcc 13.3.0 produced this assembly from this C" is such a
  relation, recorded but not stated in Lean. `Verdict` keeps proved, refuted and unknown apart.
* `Reading`: the semantic specialisation. Parse each side with a stage, and relate the results
  by a compilation `Problem` (`Silmaril.Compiler.Explorer.Problem`); `Reading.toRel` is the
  induced relation on files. A segment relation likewise is arbitrary data (`Mapping`'s points,
  or navigation edges) unless a `SegmentDiscipline` gives it a meaning.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

/-- An immutable map from file names to bytes; the first entry with a name wins. -/
abbrev Files := List (String × List UInt8)

/-- The bytes of a file. -/
def Files.read (fs : Files) (name : String) : Option (List UInt8) := fs.lookup name

/-- **A preprocessor's environment**: the files it may include, the directories searched in
order, the predefined macros (`none`: defined without a value) and the compiler options. -/
structure IncludeEnv where
  files : Files
  search : List String
  macros : List (String × Option String)
  options : List String

/-- How far a stage is to be trusted. -/
inductive Trust where
  /-- Its output is checked by the kernel against its input (a theorem). -/
  | verified
  /-- Its output is checked by compiled evaluation (`#guard`), not by the kernel. -/
  | evaluated
  /-- Its output is used as given (an external tool, an unverified reader). -/
  | trusted
  deriving Repr, DecidableEq

/-- **A stage**: a named partial function, with its trust. -/
structure Stage (α β : Type) where
  name : String
  trust : Trust
  run : α → Except String β

/-- Run one stage, then another; the composite is as trusted as its least trusted part. -/
def Stage.comp {α β γ : Type} (f : Stage α β) (g : Stage β γ) : Stage α γ where
  name := f.name ++ " ; " ++ g.name
  trust := if f.trust = .verified ∧ g.trust = .verified then .verified
    else if f.trust = .trusted ∨ g.trust = .trusted then .trusted else .evaluated
  run a := f.run a >>= g.run

/-- **A stage validated against a relation**: every output is related to its input. The
translation-validation problem of a trusted stage. -/
def Stage.validated {α β : Type} (f : Stage α β) (R : α → β → Prop) : Prop :=
  ∀ a b, f.run a = .ok b → R a b

/-- **An arbitrary relation problem**: a source, a target and a relation; nothing more. -/
structure RelProblem (α β : Type) where
  source : α
  target : β
  Rel : α → β → Prop

/-- The problem's statement. -/
def RelProblem.Statement {α β : Type} (P : RelProblem α β) : Prop := P.Rel P.source P.target

/-- What is known of a statement: proved, refuted (its negation proved) or unknown. -/
inductive Verdict (p : Prop) where
  | proved : p → Verdict p
  | refuted : ¬ p → Verdict p
  | unknown : Verdict p

/-- Whether a relation has a semantics in Lean. -/
inductive Semantics where
  /-- No semantics: the relation is recorded (a receipt, a debug table) but not stated. -/
  | none
  /-- A Lean statement (`decl` names it) relates the two sides. -/
  | stated (decl : String)
  deriving Repr, DecidableEq

/-- **A semantic reading** of files: parse each side by a stage, then relate the parses by a
compilation problem built from them. -/
structure Reading (α β σ τ R T : Type) where
  parseSource : Stage α σ
  parseTarget : Stage β τ
  problem : σ → τ → Problem σ τ R T

/-- **The relation a reading induces** on files: both sides parse, and the problem of their
parses is refined. A side that does not parse is not related. -/
def Reading.toRel {α β σ τ R T : Type} (r : Reading α β σ τ R T) (a : α) (b : β) : Prop :=
  ∃ s t, r.parseSource.run a = .ok s ∧ r.parseTarget.run b = .ok t ∧ (r.problem s t).Refines

end Silmaril.Compiler.Explorer

end
