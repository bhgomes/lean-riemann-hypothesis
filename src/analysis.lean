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

/--
-/
structure Continuation {X Y : Type*} {𝔇 : 𝒫 X} (f : Π x, 𝔇 x → Y)
    := (domain    : 𝒫 X)
       (extension : Π x, 𝔇 x → domain x)
       (map       : Π x, domain x → Y)

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
