/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    reduction.lean                                                    |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .basic

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {X : Type*} {Y : Type*} (ℱ : 𝒫 (X → Y))

/--
-/
def Reduction.action
    := Π f, ℱ f → Y

/--
-/
structure Reduction
    := (reduce : Reduction.action ℱ)

/--
-/
class PointFamily
    := (has_constants : Π y, ℱ ↓y)

/--
-/
class DifferenceFamily [has_sub Y]
    := (closure : Π f g (fℱ : ℱ f) (gℱ : ℱ g), ℱ (f - g))

namespace Reduction --———————————————————————————————————————————————————————————————————--

/--
-/
def left_closed_at (f : X → Y) (g : Y → Y)
    := ℱ f → ℱ (g ∘ f)

/--
-/
def left_closed (g : Y → Y)
    := Π f, left_closed_at ℱ f g

/--
-/
def right_closed_at (f : X → Y) (g : X → X)
    := ℱ f → ℱ (f ∘ g)

/--
-/
def right_closed (g : X → X)
    := Π f, right_closed_at ℱ f g

--———————————————————————————————————————————————————————————————————————————————————————--
variables (𝒮 : Reduction ℱ)

/--
-/
def left_factors (β : Y → Y) (lcβ : left_closed ℱ β)
    := Π f (fℱ : ℱ f), 𝒮.reduce (β ∘ f) (lcβ f fℱ) = β (𝒮.reduce f fℱ)

end Reduction --—————————————————————————————————————————————————————————————————————————--

/--
-/
structure UnitalReduction [PointFamily ℱ] extends Reduction ℱ
    := (constant_reduction : Π y, reduce ↓y (PointFamily.has_constants ℱ y) = y)

/--
-/
structure MonotonicReduction [has_le Y] extends Reduction ℱ
    := (monotonicity : Π f g {fℱ gℱ}, (f ≤ g) → (reduce f fℱ ≤ reduce g gℱ))

namespace TranslativeReduction --————————————————————————————————————————————————————————--
variables [has_le Y] [has_zero Y] [has_sub Y] [PointFamily ℱ] [DifferenceFamily ℱ]
          (reduce : Reduction.action ℱ)

open PointFamily DifferenceFamily

/--
-/
def constant_difference_property
    := Π f k {fℱ},
         reduce (f - ↓k) (closure f ↓k fℱ (has_constants _ _))
       = reduce f fℱ - reduce ↓k (has_constants _ _)

/--
-/
def translation_invariance_property
    := Π f g {fℱ gℱ}, 0 ≤ reduce (g - f) (closure g f gℱ fℱ) → reduce f fℱ ≤ reduce g gℱ

end TranslativeReduction --——————————————————————————————————————————————————————————————--

/--
-/
structure TranslativeReduction
    [has_le Y] [has_zero Y] [has_sub Y] [PointFamily ℱ] [DifferenceFamily ℱ]
    extends Reduction ℱ
    := (constant_difference    : TranslativeReduction.constant_difference_property ℱ reduce)
       (translation_invariance : TranslativeReduction.translation_invariance_property ℱ reduce)
