module

public import Silmaril.Courses.Cambridge.L2.ClosureValue
public import Mathlib.Logic.Relation

/-! # Relational store and closure denotation for CBV L2

The inductive clauses generate the least finite-return relation. Each
premise evaluates an immediate operand, applies a saved closure, or
continues iteration in the store returned by the preceding premise.
Recursive closures carry their definition environment. Application
reinstalls the closure itself and the argument in that environment.
-/

public section

namespace Silmaril.Courses.Cambridge.L2.RelationalDenotation

inductive Returns : RuntimeEnv → Expr → Store → RuntimeValue → Store → Prop where
  | int {ρ : RuntimeEnv} {s : Store} (n : Int) : Returns ρ (.int n) s (.int n) s
  | bool {ρ : RuntimeEnv} {s : Store} (b : Bool) : Returns ρ (.bool b) s (.bool b) s
  | skip {ρ : RuntimeEnv} {s : Store} : Returns ρ .skip s .unit s
  | var {ρ : RuntimeEnv} {i : Nat} {v : RuntimeValue} {s : Store} :
      ρ[i]? = some v → Returns ρ (.bvar i) s v s
  | lam {ρ : RuntimeEnv} {A : Ty} {body : Expr} {s : Store} :
      Returns ρ (.lam A body) s (.closure A body ρ) s
  | add {ρ : RuntimeEnv} {left right : Expr} {s middle finish : Store} {a b : Int} :
      Returns ρ left s (.int a) middle → Returns ρ right middle (.int b) finish →
      Returns ρ (.binary left .add right) s (.int (a + b)) finish
  | ge {ρ : RuntimeEnv} {left right : Expr} {s middle finish : Store} {a b : Int} :
      Returns ρ left s (.int a) middle → Returns ρ right middle (.int b) finish →
      Returns ρ (.binary left .ge right) s (.bool (a ≥ b)) finish
  | deref {ρ : RuntimeEnv} {loc : Loc} {s : Store} {n : Int} :
      L1.Store.lookup s loc = some n → Returns ρ (.deref loc) s (.int n) s
  | assign {ρ : RuntimeEnv} {loc : Loc} {rhs : Expr} {s finish : Store} {n : Int} :
      Returns ρ rhs s (.int n) finish → loc ∈ finish →
      Returns ρ (.assign loc rhs) s .unit (finish.insert loc n)
  | seq {ρ : RuntimeEnv} {left right : Expr} {s middle finish : Store} {v : RuntimeValue} :
      Returns ρ left s .unit middle → Returns ρ right middle v finish →
      Returns ρ (.seq left right) s v finish
  | ifTrue {ρ : RuntimeEnv} {test yes no : Expr} {s middle finish : Store} {v : RuntimeValue} :
      Returns ρ test s (.bool true) middle → Returns ρ yes middle v finish →
      Returns ρ (.cond test yes no) s v finish
  | ifFalse {ρ : RuntimeEnv} {test yes no : Expr} {s middle finish : Store} {v : RuntimeValue} :
      Returns ρ test s (.bool false) middle → Returns ρ no middle v finish →
      Returns ρ (.cond test yes no) s v finish
  | whileFalse {ρ : RuntimeEnv} {test body : Expr} {s finish : Store} :
      Returns ρ test s (.bool false) finish →
      Returns ρ (.loop test body) s .unit finish
  | whileTrue {ρ : RuntimeEnv} {test body : Expr} {s afterTest afterBody finish : Store} :
      Returns ρ test s (.bool true) afterTest → Returns ρ body afterTest .unit afterBody →
      Returns ρ (.loop test body) afterBody .unit finish →
      Returns ρ (.loop test body) s .unit finish
  | app {ρ saved : RuntimeEnv} {fn arg body : Expr} {A : Ty}
      {s afterFn afterArg finish : Store} {argument v : RuntimeValue} :
      Returns ρ fn s (.closure A body saved) afterFn →
      Returns ρ arg afterFn argument afterArg →
      Returns (argument :: saved) body afterArg v finish →
      Returns ρ (.app fn arg) s v finish
  | appRec {ρ saved : RuntimeEnv} {fn arg body : Expr} {A B : Ty}
      {s afterFn afterArg finish : Store} {argument v : RuntimeValue} :
      Returns ρ fn s (.recursive A B body saved) afterFn →
      Returns ρ arg afterFn argument afterArg →
      Returns (argument :: .recursive A B body saved :: saved) body afterArg v finish →
      Returns ρ (.app fn arg) s v finish
  | letE {ρ : RuntimeEnv} {rhs body : Expr} {A : Ty}
      {s afterRhs finish : Store} {argument v : RuntimeValue} :
      Returns ρ rhs s argument afterRhs → Returns (argument :: ρ) body afterRhs v finish →
      Returns ρ (.letE A rhs body) s v finish
  | letRec {ρ : RuntimeEnv} {fn body : Expr} {A B : Ty} {s finish : Store} {v : RuntimeValue} :
      Returns (.recursive A B fn ρ :: ρ) body s v finish →
      Returns ρ (.letRecFun A B fn body) s v finish

/-- One iteration evaluates the guard and then the body in its resulting store. -/
def LoopIteration (ρ : RuntimeEnv) (test body : Expr) (s t : Store) : Prop :=
  ∃ middle, Returns ρ test s (.bool true) middle ∧ Returns ρ body middle .unit t

private theorem Returns.while_trace {ρ : RuntimeEnv} {e test body : Expr} {s finish : Store}
    {v : RuntimeValue} (run : Returns ρ e s v finish) (shape : e = .loop test body) :
    v = .unit ∧ ∃ last, Relation.ReflTransGen (LoopIteration ρ test body) s last ∧
      Returns ρ test last (.bool false) finish := by
  induction run
  case whileFalse guard _ =>
    cases shape
    exact ⟨rfl, _, .refl, guard⟩
  case whileTrue guard body _ _ _ rest =>
    cases shape
    obtain ⟨_, last, iterations, exit⟩ := rest rfl
    exact ⟨rfl, last, .head ⟨_, guard, body⟩ iterations, exit⟩
  all_goals contradiction

/-- A returning loop consists of finitely many true iterations followed by
one false guard. Effects in that last guard are part of the final store. -/
theorem Returns.while_iff {ρ : RuntimeEnv} {test body : Expr} {s finish : Store} {v : RuntimeValue} :
    Returns ρ (.loop test body) s v finish ↔
      v = .unit ∧ ∃ last, Relation.ReflTransGen (LoopIteration ρ test body) s last ∧
        Returns ρ test last (.bool false) finish := by
  refine ⟨fun run => run.while_trace rfl, ?_⟩
  rintro ⟨rfl, last, iterations, exit⟩
  induction iterations using Relation.ReflTransGen.head_induction_on with
  | refl => exact .whileFalse exit
  | head next _ rest =>
    obtain ⟨_, guard, body⟩ := next
    exact .whileTrue guard body rest

end Silmaril.Courses.Cambridge.L2.RelationalDenotation
