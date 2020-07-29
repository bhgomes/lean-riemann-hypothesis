/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    complex.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .exponential

/-!
-/

namespace riemann_hypothesis --——————————————————————————————————————————————————————————--

/--
-/
class Algebra (α : Type*)
    extends has_zero α, has_one α, has_neg α, has_add α, has_sub α, has_mul α, has_inv α

--———————————————————————————————————————————————————————————————————————————————————————--
variables (ℂ : Type*) (ℝ : Type*)

variables [preorder ℝ] [Algebra ℝ]

variables [Algebra ℂ]

variables [has_lift_t ℝ ℂ]

/--
-/
structure Complex
    := (real_part                : ℂ → ℝ)
       (abs                      : ℂ → ℝ)
       (exp                      : ℂ → ℂ)
       (real_explog              : ExpLog ℝ ℝ)
       (abs_nonneg               : Π z, 0 ≤ abs z)
       (exp_nonzero              : Π z, exp z ≠ 0)
       (exp_homomorphism_zero    : exp 0 = 1)
       (exp_homomorphism         : Π w z, exp (w + z) = exp w * exp z)
       (exp_homomorphism_inv     : Π w z, exp (w - z) = exp w * (exp z)⁻¹)
       (real_part_scaling        : Π x z, real_part (↑x * z) = x * real_part z)
       (abs_exp_is_exp_real_part : Π z, abs (exp z) = real_explog.exp (real_part z))
       (exp_linearization        : Π x, abs x ≤ 1
                                 → Π z, abs (exp (x * z) - (x * z + 1))
                                      ≤ (abs x * abs x) * real_explog.exp (abs z))
       (real_log_bound           : Π x (p : 0 < 1 - x), abs ↑x ≤ 2⁻¹
                                      → abs ↑(real_explog.log (1 - x) p)
                                      ≤ abs ↑x + abs ↑x)

namespace Complex --—————————————————————————————————————————————————————————————————————--
variables {ℂ ℝ} (ℭ : Complex ℂ ℝ)

open algebra

/--
-/
def real_abs (x : ℝ)
    := ℭ.abs (↑x)

/--
-/
def real_exp (x)
    := ℭ.real_explog.exp x

/--
-/
def real_log (x)
    := ℭ.real_explog.log x

/--
-/
def pow (a apos x)
    := ℭ.exp (↑(ℭ.real_explog.log a apos) * x)

/--
-/
def pow_domain_irrel
    (x xpos)
    (y ypos)
    (z)
    : x = y → ℭ.pow x xpos z = ℭ.pow y ypos z :=
    begin
        intros x_eq_y,
        rw [pow, pow],
        rw ExpLog.log_domain_irrel _ _ _ _ _ x_eq_y,
    end

/--
-/
def pow_nonzero (a apos x)
    : ℭ.pow a apos x ≠ 0
    := ℭ.exp_nonzero _

/--
-/
def pow_neg_exponent_inverts
    [has_left_sub_distributivity ℂ]
    [has_mul_zero_is_zero ℂ]
    [has_left_unit ℂ]
    (a apos x)
    : ℭ.pow a apos (0 - x) = (ℭ.pow a apos x)⁻¹ :=
    begin
        rw pow,
        rw has_left_sub_distributivity.eq,
        rw has_mul_zero_is_zero.eq,
        rw exp_homomorphism_inv,
        rw exp_homomorphism_zero,
        rw has_left_unit.eq,
        rw ← pow,
    end

/--
-/
def abs_pow_is_real_pow (x xpos z)
    : ℭ.abs (ℭ.pow x xpos z) = ℭ.real_explog.pow x xpos (ℭ.real_part z)
    := by rw [pow, abs_exp_is_exp_real_part, real_part_scaling, ExpLog.pow]

--———————————————————————————————————————————————————————————————————————————————————————--
local notation `|` z `|` := ℭ.abs z

/--
-/
def one_minus_pow_bound
    [has_lift_t nat ℝ]

    [has_add_le_add ℝ]

    [has_left_unit ℝ]
    [has_right_unit ℝ]

    [has_squared_le_monotonic ℝ]

    [has_inv_mul_right_cancel_self ℝ]

    [has_le_nonneg_mul_preserves_left ℝ]
    [has_le_nonneg_mul_preserves_right ℝ]

    [has_mul_assoc ℝ]

    [has_left_add_distributivity ℝ]
    [has_right_add_distributivity ℝ]

    [has_sub_add_sub_cancel ℂ]
    [has_add_sub_assoc ℂ]
    [has_sub_self_is_zero ℂ]
    [has_zero_right_add_cancel ℂ]

    [has_zero_right_add_cancel ℝ]

    (zero_lt_two : 0 < (2 : ℝ))
    (one_le_two  : 1 ≤ (2 : ℝ))

    (abs_mul      : Π a b, |a * b| = |a| * |b|)
    (abs_triangle : Π a b, |a + b| ≤ |a| + |b|)

    (z) (x : ℝ) (abs_x_le_half : |↑x| ≤ 2⁻¹) (one_minus_x_pos : 0 < 1 - x)

    : | ℭ.pow (1 - x) one_minus_x_pos z  - 1 | ≤ |↑x| * (4 * ℭ.real_exp (|z|) + (|z| + |z|)) :=

    begin
        rw ← has_sub_add_sub_cancel.eq _ (↑(ℭ.real_log (1 - x) one_minus_x_pos) * z + 1) _,

        refine le_trans (abs_triangle _ _) _,

        rw has_add_sub_assoc.eq,
        rw has_sub_self_is_zero.eq,
        rw has_zero_right_add_cancel.eq,
        rw abs_mul,
        rw has_left_add_distributivity.eq,
        rw ← has_mul_assoc.eq,

        let log_bound
            := ℭ.real_log_bound _ one_minus_x_pos abs_x_le_half,

        let abs_x_inequality
            := has_le_nonneg_mul_preserves_left.le (le_of_lt zero_lt_two) abs_x_le_half,

        rw has_inv_mul_right_cancel_self.eq _ (ne_of_lt zero_lt_two).symm
            at abs_x_inequality,

        rw two_mul_lemma at abs_x_inequality,

        refine has_add_le_add.le
            (le_trans
                (ℭ.exp_linearization _ (le_trans log_bound abs_x_inequality) _)
                (has_le_nonneg_mul_preserves_right.le
                    (le_of_lt (ExpLog.exp_positive _ _))
                    (le_trans
                        (has_squared_le_monotonic.le (abs_nonneg _ _) log_bound) _))) _,

        rw ← two_squares_is_four_lemma',

        refine has_le_nonneg_mul_preserves_right.le _ _,

        let zero_le_four
            := has_add_le_add.le (le_of_lt zero_lt_two) (le_of_lt zero_lt_two),

        rw has_zero_right_add_cancel.eq at zero_le_four,

        refine zero_le_four,

        have abs_x_le_one : |↑x| ≤ 1,
        {
            refine le_trans _ abs_x_inequality,

            rw ← two_mul_lemma',
            rw ← has_right_unit.eq (|↑x|),
            rw has_mul_assoc.eq,
            rw has_left_unit.eq,

            refine has_le_nonneg_mul_preserves_left.le (abs_nonneg _ _) one_le_two,
        },

        let square_le_id
            := has_le_nonneg_mul_preserves_right.le (abs_nonneg _ _) abs_x_le_one,

        rw has_left_unit.eq at square_le_id,

        refine square_le_id,

        rw has_left_add_distributivity.eq,
        rw ← has_right_add_distributivity.eq,

        refine has_le_nonneg_mul_preserves_right.le (abs_nonneg _ _) log_bound,
    end

end Complex --———————————————————————————————————————————————————————————————————————————--

end riemann_hypothesis --————————————————————————————————————————————————————————————————--
