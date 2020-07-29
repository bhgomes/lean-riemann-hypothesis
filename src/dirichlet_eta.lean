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

namespace riemann_hypothesis --——————————————————————————————————————————————————————————--
variables {ℂ : Type*} {ℝ : Type*}
          [has_lift_t nat ℝ] [has_lift_t ℝ ℂ] [preorder ℝ] [Algebra ℝ] [Algebra ℂ]
          (ℭ : Complex ℂ ℝ)

namespace dirichlet_eta --———————————————————————————————————————————————————————————————--

open algebra

/--
-/
def term_pair
    [has_lift_zero_same nat ℝ]
    [has_lift_lt_comm nat ℝ]
    (s n)
    := riemann_zeta.term ℭ.pow s (2 * n) - riemann_zeta.term ℭ.pow s (2 * n).succ

namespace term_pair --———————————————————————————————————————————————————————————————————--

/--
-/
def riemann_zeta_bound (s)
    := ↑4 * ℭ.real_exp (ℭ.abs s) + ↑3 * ℭ.abs s

namespace riemann_zeta_bound --——————————————————————————————————————————————————————————--
variables [has_zero_mul_is_zero ℝ] [has_nonneg_mul_nonneg_is_nonneg ℝ]
          [has_lt_add_of_le_of_pos ℝ] [has_lt_pos_mul_preserves_right ℝ]
          [has_lift_zero_same nat ℝ] [has_lift_one_same nat ℝ]
          [has_lift_add_comm nat ℝ] [has_lift_lt_comm nat ℝ]

/--
-/
def positive (s)
    : 0 < riemann_zeta_bound ℭ s :=
    begin
        refine has_lt_add_of_le_of_pos.lt _
            (has_nonneg_mul_nonneg_is_nonneg.le
                (le_of_lt (nat.lift.succ_pos ℝ _)) (ℭ.abs_nonneg _)),

        let four_exponentials_are_positive
            := has_lt_pos_mul_preserves_right.lt
                (ℭ.real_explog.exp_positive _) (nat.lift.succ_pos ℝ _),

        rw has_zero_mul_is_zero.eq at four_exponentials_are_positive,

        refine four_exponentials_are_positive,
    end

/--
-/
def abs_positive
    (ge_zero_to_abs : Π z, 0 ≤ z → ℭ.abs ↑z = z)
    (s)
    : 0 < ℭ.abs ↑(riemann_zeta_bound ℭ s) :=
    begin
        rw ge_zero_to_abs _ (le_of_lt (positive ℭ _)),
        refine positive ℭ _,
    end

end riemann_zeta_bound --————————————————————————————————————————————————————————————————--

/--
-/
def bounded_by_riemann_zeta
    [has_add_le_add ℝ]
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
    [has_zero_mul_is_zero ℝ]
    [has_mul_zero_is_zero ℝ]
    [has_zero_right_add_cancel ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_mul_pos ℝ]
    [has_inv_pos ℝ]

    [has_lift_add_comm nat ℝ]
    [has_lift_le_comm nat ℝ]
    [has_lift_lt_comm nat ℝ]
    [has_lift_ne_comm nat ℝ]
    [has_lift_sub_comm nat ℝ]
    [has_lift_one_same nat ℝ]
    [has_lift_zero_same nat ℝ]

    [has_add_sub_assoc ℂ]
    [has_inv_mul_left_cancel_self ℂ]
    [has_left_sub_distributivity ℂ]
    [has_left_unit ℂ]
    [has_mul_assoc ℂ]
    [has_right_sub_distributivity ℂ]
    [has_right_unit ℂ]
    [has_sub_add_sub_cancel ℂ]
    [has_sub_self_is_zero ℂ]
    [has_mul_zero_is_zero ℂ]
    [has_zero_right_add_cancel ℂ]
    [has_zero_sub_is_neg ℂ]

    [has_lift_sub_comm ℝ ℂ]

    (abs_mul        : Π a b, ℭ.abs (a * b) = ℭ.abs (a) * ℭ.abs (b))
    (abs_sub        : Π a b, ℭ.abs (a - b) = ℭ.abs (b - a))
    (abs_inv        : Π z, ℭ.abs (z⁻¹) = (ℭ.abs z)⁻¹)
    (abs_add        : Π a b, ℭ.abs (a + b) ≤ ℭ.abs a + ℭ.abs b)
    (ge_zero_to_abs : Π x, 0 ≤ x → ℭ.abs ↑x = x)

    (s n)

    : ℭ.abs (term_pair ℭ s n)
        ≤ riemann_zeta.term.on_reals ℭ.real_explog (1 + ℭ.real_part s) (2 * n)
        * riemann_zeta_bound ℭ s :=

    begin
        rw [term_pair, riemann_zeta.term.on_reals],
        rw [riemann_zeta.term, riemann_zeta.term, riemann_zeta.term],
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

            rw [has_zero_mul_is_zero.eq, has_left_unit.eq] at ineq,

            refine le_of_lt ineq,
        },

        let remove_abs
            := ge_zero_to_abs _ Kinv_ge_zero,

        refine has_le_pos_mul_preserves_left.le
            (ℭ.real_explog.pow_positivity _ (nat.lift.succ_pos ℝ _) _) _,

        rw [Complex.pow, Complex.pow],
        rw ← Complex.exp_homomorphism_inv,
        rw ← has_right_sub_distributivity.eq,
        rw ← has_lift_sub_comm.eq,

        rw ← ℭ.real_explog.log_homomorphism_inv
            (nat.lift.succ_pos ℝ _) (nat.lift.succ_pos ℝ _),

        rw ← Complex.pow,

        rw ℭ.pow_domain_irrel
            (↑((2 * n).succ) * (↑((2 * n).succ.succ))⁻¹) _
            (1 - (↑(2 * n).succ.succ)⁻¹) _
            _ (by rw mul_inv_add_one_lemma),

        refine le_trans _
            (has_le_pos_mul_preserves_right.le (riemann_zeta_bound.positive _ _)
            (has_inv_reverses_le.le (le_of_lt (has_lift_lt_comm.lt
                (nat.lt_succ_self _))))),

        rw ← mul_inv_add_one_lemma,

        refine has_mul_pos.lt
            (nat.lift.succ_pos ℝ _)
            (has_inv_pos.lt (nat.lift.succ_pos ℝ _)),

        rw abs_sub,
        rw riemann_zeta_bound,
        rw has_left_add_distributivity.eq,

        refine le_trans (Complex.one_minus_pow_bound _ _ _ abs_mul abs_add _ _ _ _) _,

        rw two_is_lifted_two_lemma nat ℝ,

        refine nat.lift.succ_pos ℝ _,

        rw two_is_lifted_two_lemma nat ℝ,
        rw one_is_lifted_one_lemma nat ℝ,

        refine has_lift_le_comm.le (le_of_lt (nat.lt_succ_self _)),

        rw remove_abs,
        rw two_is_lifted_two_lemma nat ℝ,

        refine has_inv_reverses_le.le
            (has_lift_le_comm.le (nat.smallest_positive_even _)),

        rw remove_abs,
        rw ← has_left_add_distributivity.eq,

        rw four_is_lifted_four_lemma nat ℝ,
        rw ← two_mul_lemma,

        refine has_le_nonneg_mul_preserves_left.le
            Kinv_ge_zero
            (has_add_le_add.le
                (le_refl _) (has_le_nonneg_mul_preserves_right.le (ℭ.abs_nonneg _) _)),

        rw two_is_lifted_two_lemma nat ℝ,

        refine has_lift_le_comm.le (le_of_lt (nat.lt_succ_self _)),
    end

end term_pair --—————————————————————————————————————————————————————————————————————————--

/--
-/
def partial_pairs
    [has_lift_lt_comm nat ℝ]
    [has_lift_zero_same nat ℝ]
    (s)
    := partial_sum (term_pair ℭ s)

/--
-/
def partial_pairs.is_cauchy
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
    [has_sub_self_is_zero ℝ]
    [has_sub_ne_zero_of_ne ℝ]
    [has_sub_sub ℝ]
    [has_zero_mul_is_zero ℝ]
    [has_mul_zero_is_zero ℝ]
    [has_zero_left_add_cancel ℝ]
    [has_zero_right_add_cancel ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_mul_pos ℝ]
    [has_inv_pos ℝ]
    [has_sub_pos ℝ]

    [has_lift_zero_same nat ℝ]
    [has_lift_one_same nat ℝ]
    [has_lift_add_comm nat ℝ]
    [has_lift_mul_comm nat ℝ]
    [has_lift_sub_comm nat ℝ]
    [has_lift_le_comm nat ℝ]
    [has_lift_lt_comm nat ℝ]
    [has_lift_ne_comm nat ℝ]

    [has_add_sub_assoc ℂ]
    [has_inv_mul_left_cancel_self ℂ]
    [has_left_sub_distributivity ℂ]
    [has_left_unit ℂ]
    [has_mul_assoc ℂ]
    [has_right_sub_distributivity ℂ]
    [has_right_unit ℂ]
    [has_sub_add_sub_cancel ℂ]
    [has_sub_self_is_zero ℂ]
    [has_mul_zero_is_zero ℂ]
    [has_zero_right_add_cancel ℂ]
    [has_zero_sub_is_neg ℂ]

    [has_lift_zero_same ℝ ℂ]
    [has_lift_one_same ℝ ℂ]
    [has_lift_add_comm ℝ ℂ]
    [has_lift_sub_comm ℝ ℂ]
    [has_lift_mul_comm ℝ ℂ]
    [has_lift_inv_comm ℝ ℂ]

    (abs_zero abs_one)
    (abs_add : Π w z, ℭ.abs (w + z) ≤ ℭ.abs w + ℭ.abs z)
    (abs_sub : Π w z, ℭ.abs (w - z) = ℭ.abs (z - w))
    (abs_mul : Π w z, ℭ.abs (w * z) = ℭ.abs w * ℭ.abs z)
    (abs_inv : Π z, ℭ.abs (z⁻¹) = (ℭ.abs z)⁻¹)
    (abs_ge_zero)

    (pos_to_absℝ abs_monoℝ)

    (half ceil)

    (s) (σpos : 0 < ℭ.real_part s)

    : is_cauchy ℭ.abs (partial_pairs ℭ s) :=

    begin
        let one_plus_σ_gt_one := has_add_left_lt.lt _ _ 1 σpos,

        rw has_zero_right_add_cancel.eq at one_plus_σ_gt_one,

        have abs_zeroℝ : ℭ.abs ↑(0 : ℝ) = 0,
            rw has_lift_zero_same.eq,
            refine abs_zero,

        have abs_oneℝ : ℭ.abs ↑(1 : ℝ) = 1,
            rw has_lift_one_same.eq,
            refine abs_one,

        have abs_addℝ : Π x y : ℝ, ℭ.abs ↑(x + y) ≤ ℭ.abs ↑x + ℭ.abs ↑y,
            intros,
            rw has_lift_add_comm.eq,
            refine abs_add _ _,

        have abs_subℝ : Π x y : ℝ, ℭ.abs ↑(x - y) = ℭ.abs ↑(y - x),
            intros,
            rw [has_lift_sub_comm.eq, has_lift_sub_comm.eq],
            refine abs_sub _ _,

        have abs_mulℝ : Π x y : ℝ, ℭ.abs ↑(x * y) = ℭ.abs ↑x * ℭ.abs ↑y,
            intros,
            rw has_lift_mul_comm.eq,
            refine abs_mul _ _,

        have abs_invℝ : Π x : ℝ, ℭ.abs ↑(x⁻¹) = (ℭ.abs ↑x)⁻¹,
            intros,
            rw has_lift_inv_comm.eq,
            refine abs_inv _,

        refine is_cauchy.comparison _ pos_to_absℝ _ abs_zero abs_add abs_ge_zero _ _
            (term_pair.bounded_by_riemann_zeta _
                abs_mul abs_sub abs_inv abs_add pos_to_absℝ _)
            (is_cauchy.closed.partial_sum_right_mul _ abs_mulℝ _ _
                (term_pair.riemann_zeta_bound.abs_positive _ pos_to_absℝ _)
                (is_cauchy.closed.scaled_sequence_partial_sum _ abs_monoℝ _
                    (riemann_zeta.term.on_reals.nonneg _ _) _ (nat.zero_lt_one_add _)
                    (riemann_zeta.partial.on_reals.is_cauchy _ _
                        abs_zeroℝ abs_oneℝ abs_addℝ abs_subℝ abs_mulℝ abs_invℝ
                        (λ _, abs_ge_zero _) pos_to_absℝ
                        half ceil _
                        one_plus_σ_gt_one))),
    end

end dirichlet_eta --—————————————————————————————————————————————————————————————————————--
end riemann_hypothesis --————————————————————————————————————————————————————————————————--
