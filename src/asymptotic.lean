/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    asymptotic.lean                                                   |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .basic

/-!
-/

/--
-/
class has_bigO (X : Type*)
    := (O : X → 𝒫 X)

notation `𝒪` := has_bigO.O
notation f `≪` g := 𝒪 g f
notation f `≫` g := 𝒪 f g

/--
-/
class ONotation {X : Type*} [has_bigO X] [has_sub X] [has_mul X] (max : X → X → X)
    := (unit       : Π f : X, f ≪ f)
       (scaling    : Π {a b f g : X}, (f ≪ a) → (g ≪ b) → ((f * g) ≪ (a * b)))
       (difference : Π {a b f g : X}, (f ≪ a) → (g ≪ b) → ((max f g) ≪ (a - b)))

