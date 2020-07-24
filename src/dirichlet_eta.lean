/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    dirichlet_eta.lean                                                |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .complex
import .riemann_zeta

/-!
-/

namespace dirichlet_eta --———————————————————————————————————————————————————————————————--
variables {ℂ : Type*} {ℝ : Type*}
          [has_lift_t nat ℝ] [has_lift_t ℝ ℂ] [preorder ℝ] [Algebra ℝ] [Algebra ℂ]
          (ℭ : Complex ℂ ℝ)

local notation `|` z `|` := ℭ.abs z

/--
-/
def term
    [has_same_lifted_zero ℕ ℝ]
    [has_lift_lt_preserved ℕ ℝ]
    (s n)
    := ℭ.pow ↑(nat.succ           (2 * n))  (nat.lift.succ_pos ℝ _) (-s)
     - ℭ.pow ↑(nat.succ (nat.succ (2 * n))) (nat.lift.succ_pos ℝ _) (-s)

/--
-/
def term.riemann_zeta_bound (s)
    := 4 * ℭ.real_exp (|s|) + 3 * ℭ.abs s

/--
-/
def term.riemann_zeta_bound.positive
    [has_zero_left_absorb ℝ]
    [has_nonneg_mul_nonneg_is_nonneg ℝ]
    [has_lt_add_of_le_of_pos ℝ]
    [has_lt_pos_mul_preserves_right ℝ]

    [has_same_lifted_zero ℕ ℝ]
    [has_same_lifted_one ℕ ℝ]
    [has_lift_add_distributivity ℕ ℝ]
    [has_lift_lt_preserved ℕ ℝ]

    (s)

    : 0 < term.riemann_zeta_bound ℭ s :=

    begin
        have zero_lt_three : (0 : ℝ) < 3,
        {
            rw three_is_lifted_three_lemma ℕ ℝ,
            refine nat.lift.succ_pos ℝ _,
        },

        have zero_lt_four : (0 : ℝ) < 4,
        {
            rw four_is_lifted_four_lemma ℕ ℝ,
            refine nat.lift.succ_pos ℝ _,
        },

        refine has_lt_add_of_le_of_pos.lt _
            (has_nonneg_mul_nonneg_is_nonneg.le (le_of_lt zero_lt_three) (ℭ.abs_nonneg _)),

        let four_exponentials_are_positive
            := has_lt_pos_mul_preserves_right.lt
                (ℭ.real_explog.exp_positive _) zero_lt_four,

        rw has_zero_left_absorb.eq at four_exponentials_are_positive,

        refine four_exponentials_are_positive,
    end

/--
-/
def term.riemann_zeta_bound.abs_positive
    [has_zero_left_absorb ℝ]
    [has_nonneg_mul_nonneg_is_nonneg ℝ]
    [has_lt_add_of_le_of_pos ℝ]
    [has_lt_pos_mul_preserves_right ℝ]

    [has_same_lifted_zero ℕ ℝ]
    [has_same_lifted_one ℕ ℝ]
    [has_lift_add_distributivity ℕ ℝ]
    [has_lift_lt_preserved ℕ ℝ]

    (ge_zero_to_abs : Π z, 0 ≤ z → |↑z| = z)

    (s)

    : 0 < ℭ.abs ↑(term.riemann_zeta_bound ℭ s)

    := begin
        rw ge_zero_to_abs _ (le_of_lt (term.riemann_zeta_bound.positive ℭ s)),
        refine term.riemann_zeta_bound.positive ℭ _,
    end

/--
-/
def term.bounded_by_riemann_zeta
    [has_add_le_add ℝ]
    [has_inv_mul_left_cancel_self ℝ]
    [has_inv_mul_reverse ℝ]
    [has_inv_mul_right_cancel_self ℝ]
    [has_inv_reverses_le ℝ]
    [has_le_nonneg_mul_preserves_left ℝ]
    [has_le_nonneg_mul_preserves_right ℝ]
    [has_le_pos_mul_preserves_left ℝ]
    [has_le_pos_mul_preserves_right ℝ]
    [has_left_add_distributivity ℝ]
    [has_left_sub_distributivity ℝ]
    [has_left_unit ℝ]
    [has_lt_add_of_le_of_pos ℝ]
    [has_lt_pos_mul_preserves_right ℝ]
    [has_mul_assoc ℝ]
    [has_nonneg_mul_nonneg_is_nonneg ℝ]
    [has_right_add_distributivity ℝ]
    [has_right_inv_pos_lt ℝ]
    [has_right_sub_distributivity ℝ]
    [has_right_unit ℝ]
    [has_squared_le_monotonic ℝ]
    [has_zero_left_absorb ℝ]
    [has_zero_right_absorb ℝ]
    [has_zero_right_add_cancel ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_inv_ne_zero ℝ]
    [has_mul_ne_zero ℝ]
    [has_mul_pos ℝ]
    [has_inv_pos ℝ]

    [has_lift_add_distributivity nat ℝ]
    [has_lift_le_preserved nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    [has_lift_ne_preserved nat ℝ]
    [has_lift_sub_distributivity nat ℝ]
    [has_same_lifted_one nat ℝ]
    [has_same_lifted_zero nat ℝ]

    [has_add_sub_assoc ℂ]
    [has_inv_mul_left_cancel_self ℂ]
    [has_left_sub_distributivity ℂ]
    [has_left_unit ℂ]
    [has_mul_assoc ℂ]
    [has_right_sub_distributivity ℂ]
    [has_right_unit ℂ]
    [has_sub_add_sub_cancel ℂ]
    [has_sub_cancel_to_zero ℂ]
    [has_zero_right_absorb ℂ]
    [has_zero_right_add_cancel ℂ]
    [has_zero_sub_is_neg ℂ]

    [has_lift_sub_distributivity ℝ ℂ]

    (abs_mul        : Π a b, ℭ.abs (a * b) = ℭ.abs (a) * ℭ.abs (b))
    (abs_sub        : Π a b, ℭ.abs (a - b) = ℭ.abs (b - a))
    (abs_inv        : Π z, ℭ.abs (z⁻¹) = (ℭ.abs z)⁻¹)
    (abs_triangle   : Π a b, ℭ.abs (a + b) ≤ ℭ.abs a + ℭ.abs b)
    (ge_zero_to_abs : Π x, 0 ≤ x → ℭ.abs ↑x = x)

    (s n)

    : ℭ.abs (term ℭ s n)
        ≤ riemann_zeta.term.on_reals ℭ.real_explog (1 + ℭ.real_part s) (2 * n)
        * term.riemann_zeta_bound ℭ s :=

    begin
        rw [term, riemann_zeta.term.on_reals],
        rw [← has_zero_sub_is_neg.eq, ← has_zero_sub_is_neg.eq],
        rw ExpLog.pow_neg_exponent_inverts,
        rw ExpLog.pow_homomorphism,
        rw has_inv_mul_reverse.eq,
        rw ℭ.real_explog.pow_id_at_one _ (nat.lift.succ_pos ℝ _),
        rw Complex.pow_neg_exponent_inverts,
        rw Complex.pow_neg_exponent_inverts,
        rw inv_sub_inv_lemma' (ℭ.pow_nonzero _ _ _),
        rw abs_mul,
        rw abs_inv,
        rw Complex.abs_pow_is_real_pow,
        rw has_mul_assoc.eq,
        rw ← ExpLog.pow_neg_exponent_inverts,

        let K := (↑(2 * n).succ.succ : ℝ),

        have Kinv_ge_zero : K⁻¹ ≥ 0,
        {
            let ineq
                := has_right_inv_pos_lt.lt
                    (nat.lift.succ_pos ℝ _) (nat.lift.zero_lt_one ℝ),

            rw [has_zero_left_absorb.eq, has_left_unit.eq] at ineq,

            refine le_of_lt ineq,
        },

        let remove_abs
            := ge_zero_to_abs _ Kinv_ge_zero,

        refine has_le_pos_mul_preserves_left.le
            (ℭ.real_explog.pow_positivity _ (nat.lift.succ_pos ℝ _) _) _,

        rw [Complex.pow, Complex.pow],
        rw ← Complex.exp_homomorphism_inv,
        rw ← has_right_sub_distributivity.eq,
        rw ← has_lift_sub_distributivity.eq,

        rw ← ℭ.real_explog.log_homomorphism_inv
            (nat.lift.succ_pos ℝ _) (nat.lift.succ_pos ℝ _),

        rw ← Complex.pow,

        rw ℭ.pow_domain_irrel
            (↑((2 * n).succ) * (↑((2 * n).succ.succ))⁻¹) _
            (1 - (↑(2 * n).succ.succ)⁻¹) _
            _ (by rw mul_inv_add_one_lemma),

        refine le_trans _
            (has_le_pos_mul_preserves_right.le (term.riemann_zeta_bound.positive _ _)
            (has_inv_reverses_le.le (le_of_lt (has_lift_lt_preserved.lt
                (nat.lt_succ_self _))))),

        rw ← mul_inv_add_one_lemma,

        refine has_mul_pos.lt
            (nat.lift.succ_pos ℝ _)
            (has_inv_pos.lt (nat.lift.succ_pos ℝ _)),

        rw abs_sub,
        rw term.riemann_zeta_bound,
        rw has_left_add_distributivity.eq,

        refine le_trans (Complex.one_minus_pow_bound _ _ _ abs_mul abs_triangle _ _ _ _) _,

        rw two_is_lifted_two_lemma ℕ ℝ,

        refine nat.lift.succ_pos ℝ _,

        rw two_is_lifted_two_lemma ℕ ℝ,
        rw one_is_lifted_one_lemma ℕ ℝ,

        refine has_lift_le_preserved.le (le_of_lt (nat.lt_succ_self _)),

        rw remove_abs,
        rw two_is_lifted_two_lemma ℕ ℝ,

        refine has_inv_reverses_le.le
            (has_lift_le_preserved.le (nat.smallest_positive_even _)),

        rw remove_abs,
        rw ← has_left_add_distributivity.eq,

        refine has_le_nonneg_mul_preserves_left.le
            Kinv_ge_zero
            (has_add_le_add.le
                (le_refl _) (has_le_nonneg_mul_preserves_right.le (ℭ.abs_nonneg _) _)),

        rw three_is_lifted_three_lemma ℕ ℝ,
        rw two_is_lifted_two_lemma ℕ ℝ,

        refine has_lift_le_preserved.le (le_of_lt (nat.lt_succ_self _)),
    end

/--
-/
def partial.is_cauchy
    [has_add_le_add ℝ]
    [has_add_left_lt ℝ]
    [has_add_lt_add ℝ]
    [has_add_nonneg ℝ]
    [has_add_sub_assoc ℝ]
    [has_add_sub_exchange ℝ]
    [has_inv_mul_left_cancel_self ℝ]
    [has_inv_mul_reverse ℝ]
    [has_inv_mul_right_cancel_self ℝ]
    [has_inv_reverses_le ℝ]
    [has_inv_reverses_lt ℝ]
    [has_inv_right_mul_lt_pos ℝ]
    [has_le_add_of_nonneg_of_le ℝ]
    [has_le_nonneg_mul_preserves_left ℝ]
    [has_le_nonneg_mul_preserves_right ℝ]
    [has_le_pos_mul_preserves_left ℝ]
    [has_le_pos_mul_preserves_right ℝ]
    [has_le_sub_add_le ℝ]
    [has_left_add_distributivity ℝ]
    [has_left_mul_inv_lt_neg ℝ]
    [has_left_mul_inv_lt_pos ℝ]
    [has_left_sub_distributivity ℝ]
    [has_left_unit ℝ]
    [has_lt_add_of_le_of_pos ℝ]
    [has_lt_pos_mul_preserves_right ℝ]
    [has_lt_sub_neg ℝ]
    [has_mul_assoc ℝ]
    [has_nonneg_mul_nonneg_is_nonneg ℝ]
    [has_pos_mul_neg_is_neg ℝ]
    [has_right_add_distributivity ℝ]
    [has_right_inv_pos_lt ℝ]
    [has_right_sub_distributivity ℝ]
    [has_right_unit ℝ]
    [has_squared_le_monotonic ℝ]
    [has_sub_add_sub_cancel ℝ]
    [has_sub_cancel_to_zero ℝ]
    [has_sub_ne_zero_of_ne ℝ]
    [has_sub_sub ℝ]
    [has_zero_left_absorb ℝ]
    [has_zero_left_add_cancel ℝ]
    [has_zero_right_absorb ℝ]
    [has_zero_right_add_cancel ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_inv_ne_zero ℝ]
    [has_mul_ne_zero ℝ]
    [has_zero_ne_one ℝ]
    [has_mul_pos ℝ]
    [has_inv_pos ℝ]
    [has_sub_pos ℝ]
    [has_zero_lt_one ℝ]

    [has_lift_add_distributivity nat ℝ]
    [has_lift_le_preserved nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    [has_lift_mul_distributivity nat ℝ]
    [has_lift_ne_preserved nat ℝ]
    [has_lift_sub_distributivity nat ℝ]
    [has_same_lifted_one nat ℝ]
    [has_same_lifted_zero nat ℝ]

    [has_add_sub_assoc ℂ]
    [has_inv_mul_left_cancel_self ℂ]
    [has_left_sub_distributivity ℂ]
    [has_left_unit ℂ]
    [has_mul_assoc ℂ]
    [has_right_sub_distributivity ℂ]
    [has_right_unit ℂ]
    [has_sub_add_sub_cancel ℂ]
    [has_sub_cancel_to_zero ℂ]
    [has_zero_right_absorb ℂ]
    [has_zero_right_add_cancel ℂ]
    [has_zero_sub_is_neg ℂ]

    [has_lift_sub_distributivity ℝ ℂ]

    (abs_zeroℂ abs_mulℂ abs_subℂ abs_invℂ abs_triangleℂ abs_nonnegℂ)
    (abs_zero abs_one abs_triangle abs_sub abs_mul abs_inv abs_nonneg)

    (pos_to_abs abs_mono)

    (half ceil)

    (s) (σpos : 0 < ℭ.real_part s)

    : is_cauchy ℭ.abs (partial_sum (term ℭ s)) :=

    begin
        let one_plus_σ_gt_one := has_add_left_lt.lt _ _ 1 σpos,

        rw has_zero_right_add_cancel.eq at one_plus_σ_gt_one,

        refine is_cauchy.comparison _ pos_to_abs _
            abs_zeroℂ abs_triangleℂ abs_nonnegℂ _ _
                (term.bounded_by_riemann_zeta _
                    abs_mulℂ abs_subℂ abs_invℂ abs_triangleℂ pos_to_abs _)
                (is_cauchy.closed.partial_sum_right_mul _ abs_mul _ _
                    (term.riemann_zeta_bound.abs_positive _ pos_to_abs _)
                    (is_cauchy.closed.scaled_sequence_partial_sum _ abs_mono _
                        (riemann_zeta.term.on_reals.nonneg _ _) _ (nat.zero_lt_one_add _)
                        (riemann_zeta.partial.on_reals.is_cauchy _ _
                            abs_zero abs_one abs_triangle abs_sub abs_mul abs_inv
                            abs_nonneg pos_to_abs half ceil _
                            one_plus_σ_gt_one))),
    end

/- TODO:
def cauchy_sequence (s σpos) : CauchySequence ℭ.abs
    := { sequence  := partial ℭ.pow s,
         condition := partial.is_cauchy ℭ s σpos }
-/

end dirichlet_eta --—————————————————————————————————————————————————————————————————————--
