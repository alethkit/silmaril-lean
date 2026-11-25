module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PositionedRuntime.LeftPorts.Thms
import Mathlib.Tactic.Positivity

@[expose] public noncomputable section

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

universe u v
variable {O : Type u}

/-- An admissible cap for any finite ordered word, including the empty word. -/
def evenlySpaced (S : Signature.{u,v} O) (word : List O) : FixedCap S where
  profile :=
    { size := word.length
      label := word.get
      x i := ((i.val : ℝ) + 1) / ((word.length : ℝ) + 1)
      ordered := by
        intro i j less
        apply div_lt_div_of_pos_right _ (by positivity)
        exact (add_lt_add_iff_right (1 : ℝ)).2 (by exact_mod_cast (show i.val < j.val from less)) }
  inside i := by
    change ((i.val : ℝ) + 1) / ((word.length : ℝ) + 1) ∈ Set.Ioo 0 1
    constructor
    · exact div_pos (by positivity) (by positivity)
    · rw [div_lt_one (by positivity)]
      exact_mod_cast Nat.add_lt_add_right i.isLt 1

theorem evenlySpaced_types (S : Signature.{u,v} O) (word : List O) :
    (evenlySpaced S word).types = word := by exact List.ofFn_get word

end Silmaril.RuntimeWires.ProgressiveGraph.FixedCap

namespace Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap

open CategoryTheory Presentation

universe u v
variable {G : EffectfulPolygraph.{u,v}}

/-- Geometric choices for iterated single-value left placement. Each step
chooses its own two outer cuts and through-contact profiles. The tail is
placed first, so the new idle value is at the left of the entire tail. -/
inductive LeftPlacement (X Y : FixedRuntimeCap G) :
    List G.Obj → FixedCap (signature G) → FixedCap (signature G) → Type (max u v) where
  | nil : LeftPlacement X Y [] X.cap Y.cap
  | cons {w : List G.Obj} {A B C D : FixedCap (signature G)}
      (tail : LeftPlacement X Y w A B) (x : G.Obj) (idle lower upper : FixedCap (signature G))
      (idleTypes : idle.types = [some x]) (lowerTypes : lower.types = values (w ++ X.word))
      (upperTypes : upper.types = values (w ++ Y.word))
      (input : C.types = none :: values ((x :: w) ++ X.word))
      (output : D.types = none :: values ((x :: w) ++ Y.word)) :
      LeftPlacement X Y (x :: w) C D

namespace LeftPlacement

variable {X Y : FixedRuntimeCap G} {w : List G.Obj} {A B : FixedCap (signature G)}

theorem input_types (plan : LeftPlacement X Y w A B) : A.types = none :: values (w ++ X.word) :=
  match plan with
  | .nil => X.types
  | .cons _ _ _ _ _ _ _ _ input _ => input

theorem output_types (plan : LeftPlacement X Y w A B) : B.types = none :: values (w ++ Y.word) :=
  match plan with
  | .nil => Y.types
  | .cons _ _ _ _ _ _ _ _ _ output => output

/-- The decorated input cap retains its actual coordinates and ordered word. -/
def source (plan : LeftPlacement X Y w A B) : FixedRuntimeCap G :=
  ⟨A, w ++ X.word, plan.input_types⟩

/-- The decorated output cap uses the independently chosen target cut. -/
def target (plan : LeftPlacement X Y w A B) : FixedRuntimeCap G :=
  ⟨B, w ++ Y.word, plan.output_types⟩

/-- Insert one lower and one upper crossing per idle letter by collared
placement. The empty word uses the original drawing. -/
def drawing {w : List G.Obj} {A B : FixedCap (signature G)} (plan : LeftPlacement X Y w A B)
    (p : FixedDrawing (signature G) X.cap.profile Y.cap.profile) :
    FixedDrawing (signature G) A.profile B.profile :=
  match plan with
  | .nil => p
  | .cons tail x idle lower upper idleTypes lowerTypes upperTypes input output =>
    placeLeftDrawing (X := tail.source) (Y := tail.target) x idle lower upper
      idleTypes lowerTypes upperTypes input output (tail.drawing p)

/-- Prepend a value with given outer cuts and evenly spaced idle and
through-contact profiles. Use `cons` to specify those profiles as well. -/
def withOuterCuts (tail : LeftPlacement X Y w A B) (x : G.Obj) {C D : FixedCap (signature G)}
    (input : C.types = none :: values ((x :: w) ++ X.word))
    (output : D.types = none :: values ((x :: w) ++ Y.word)) :
    LeftPlacement X Y (x :: w) C D :=
  .cons tail x (FixedCap.evenlySpaced _ [some x])
    (FixedCap.evenlySpaced _ (values (w ++ X.word))) (FixedCap.evenlySpaced _ (values (w ++ Y.word)))
    (FixedCap.evenlySpaced_types _ _) (FixedCap.evenlySpaced_types _ _) (FixedCap.evenlySpaced_types _ _)
    input output

/-- Every word admits a placement. These choices leave the original
input and output cuts of the active drawing as supplied. -/
def withDefaultCuts (X Y : FixedRuntimeCap G) (word : List G.Obj) :
    Σ A B : FixedCap (signature G), LeftPlacement X Y word A B :=
  match word with
  | [] => ⟨X.cap, Y.cap, .nil⟩
  | x :: tail =>
    ⟨FixedCap.evenlySpaced _ (none :: values ((x :: tail) ++ X.word)),
      FixedCap.evenlySpaced _ (none :: values ((x :: tail) ++ Y.word)),
      (withDefaultCuts X Y tail).2.2.withOuterCuts x
        (FixedCap.evenlySpaced_types _ _) (FixedCap.evenlySpaced_types _ _)⟩

end LeftPlacement
end Silmaril.RuntimeWires.ProgressiveGraph.FixedRuntimeCap
