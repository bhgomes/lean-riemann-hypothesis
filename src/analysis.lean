/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    analysis.lean                                                     |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .reduction

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {X : Type*} {Y : Type*}

/--
-/
def supp [has_zero Y] (f : X → Y)
    := λ x, f x ≠ 0

/--
-/
structure Continuation {𝔇 : 𝒫 X} (f : Π x, 𝔇 x → Y)
    := (domain    : 𝒫 X)
       (extension : Π x, 𝔇 x → domain x)
       (map       : Π x, domain x → Y)

/--
-/
class is_schwartz (bounded : 𝒫 Y) (is_smooth : 𝒫 (X → Y)) (schwartz_constant : ℕ → ℕ → (X → Y) → Y) (f : X → Y)
    := (smooth                    : is_smooth f)
       (bounded_schwarz_constants : Π m n, bounded (schwartz_constant m n f))

/--
-/
def extends_to_schwartz : (X → Y) → 𝒫 Y → Type*
    := sorry

namespace LFunction --———————————————————————————————————————————————————————————————————--
variables {I : Type*} {C : Type*}
          [has_one C] [has_neg C] [has_mul C]
          {summable : 𝒫 (I → C)} (Sum : Reduction summable)
          (pow : I → C → C) (χ : I → C) (s : C)

/--
-/
def series_term
    := λ n, χ n * pow n (-s)

/--
-/
def series_convergence_criterion
    := summable (series_term pow χ s)

/--
-/
def series (convergence : series_convergence_criterion pow χ s)
    := Sum.reduce (series_term pow χ s) convergence

end LFunction --—————————————————————————————————————————————————————————————————————————--

/--
-/
structure LFunction {I C : Type*}
    [has_one C] [has_neg C] [has_mul C]
    {summable : 𝒫 (I → C)} (Sum : Reduction summable)
    (pow : I → C → C)
    := (character    : I → C)
       (continuation : Continuation (LFunction.series Sum pow character))
