/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    riemann_hypothesis.lean                                           |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .dirichlet_eta

/-!
-/

namespace riemann_hypothesis --——————————————————————————————————————————————————————————--
variables {ℂ : Type*} {ℝ : Type*}
          [has_lift_t nat ℝ] [has_lift_t ℝ ℂ] [preorder ℝ] [Algebra ℝ] [Algebra ℂ]
          (ℭ : Complex ℂ ℝ)

open algebra

/--
-/
def form.dirichlet_eta
    [has_lift_zero_same nat ℝ]
    [has_lift_lt_comm nat ℝ]
    (s) (σpos : 0 < ℭ.real_part s)
    := is_convergent ℭ.abs (dirichlet_eta.partial_pairs ℭ s) 0 → ℭ.real_part s = 2⁻¹

end riemann_hypothesis --————————————————————————————————————————————————————————————————--
