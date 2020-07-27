/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    riemann_zeta.lean                                                 |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .cauchy

/-!
-/

namespace riemann_zeta --————————————————————————————————————————————————————————————————--
variables {ℝ : Type*}
          [has_lift_t nat ℝ] [preorder ℝ] [has_zero ℝ] [has_one ℝ]
          [has_neg ℝ] [has_add ℝ] [has_sub ℝ] [has_mul ℝ] [has_inv ℝ]

/--
-/
def term {α β γ}
    [has_zero α]
    [has_lt α]
    [has_lift_t nat α]
    [has_same_lifted_zero nat α]
    [has_lift_lt_preserved nat α]
    [has_neg β]
    (pow : Π a : α, 0 < a → β → γ)
    (s n)
    := pow ↑(nat.succ n) (nat.lift.succ_pos α _) (-s)

namespace term --——————————————————————————————————————————————————————————————————————————--

/--
`ζ` Series Term for Real Inputs

`ζₙ(σ) := (n+1) ^ -σ`
-/
def on_reals
    [has_same_lifted_zero nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    (ℯ : ExpLog ℝ ℝ)
    (σ n)
    := term ℯ.pow σ n

/--
-/
def on_reals.nonneg
    [has_same_lifted_zero ℕ ℝ]
    [has_lift_lt_preserved ℕ ℝ]
    (ℯ : ExpLog ℝ ℝ)
    (σ n)
    : 0 ≤ on_reals ℯ σ n
    := le_of_lt (ExpLog.exp_positive _ _)

/--
-/
def on_reals.non_increasing
    [has_left_unit ℝ]
    [has_zero_right_absorb ℝ]
    [has_left_sub_distributivity ℝ]
    [has_inv_reverses_lt ℝ]
    [has_lt_pos_mul_preserves_right ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_lift_lt_preserved nat ℝ]
    [has_same_lifted_zero ℕ ℝ]
    (ℯ : ExpLog ℝ ℝ)
    (σ σpos)
    : non_increasing (on_reals ℯ σ) :=
    begin
        intros _,

        rw [on_reals, on_reals, term, term],
        rw ← has_zero_sub_is_neg.eq,
        rw [ExpLog.pow_neg_exponent_inverts, ExpLog.pow_neg_exponent_inverts],

        refine le_of_lt
            (has_inv_reverses_lt.lt
                (ExpLog.pow_monotonic _ _ _ σpos
                    (has_lift_lt_preserved.lt (nat.lt_succ_self _)))),
    end

/--
-/
def on_reals.rewrite.pow_reduction
    [has_left_add_distributivity ℝ]
    [has_right_add_distributivity ℝ]
    [has_left_sub_distributivity ℝ]

    [has_left_unit ℝ]
    [has_right_unit ℝ]

    [has_zero_left_absorb ℝ]
    [has_zero_right_absorb ℝ]

    [has_zero_sub_is_neg ℝ]

    [has_mul_pos ℝ]

    [has_same_lifted_one nat ℝ]
    [has_same_lifted_zero nat ℝ]
    [has_lift_add_distributivity nat ℝ]
    [has_lift_mul_distributivity nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    [has_lift_le_preserved nat ℝ]

    (ℯ : ExpLog ℝ ℝ)

    (σ) (n : nat)

    : ↑(2 ^ n) * on_reals ℯ σ (2 ^ n - 1)
    = ℯ.pow (ℯ.pow ↑2 _ (1 - σ)) (ℯ.pow_positivity _ (nat.lift.succ_pos ℝ _) _) ↑n :=

    begin
        have lifted_pow2_pos : Π k : nat, 0 < (↑(2 ^ k) : ℝ),
            intros k,
            refine (lt_of_lt_of_le (nat.lift.zero_lt_one ℝ) _),
            rw one_is_lifted_one_lemma ℕ ℝ,
            refine has_lift_le_preserved.le (nat.pow_two_ge_one _),

        rw [on_reals, term],
        rw ← ℯ.pow_id_at_one ↑(_) (lifted_pow2_pos _),

        rw ExpLog.pow_domain_irrel _
            ↑(nat.succ (2 ^ n - 1)) _ _ (lifted_pow2_pos _) _
            (by rw [nat.succ_eq_add_one, nat.sub_add_cancel (nat.pow_two_ge_one _)]),

        rw ℯ.pow_homomorphism_inv_from_neg,

        induction n with n hn,
            rw has_same_lifted_zero.eq,
            rw ExpLog.pow_homomorphism_zero,

            rw ExpLog.pow_domain_irrel _ ↑(2 ^ 0) _ (1 : ℝ) _ _
                (by rw [nat.pow_zero, has_same_lifted_one.eq]),

            rw ExpLog.pow_homomorphism_one,

            rw ℯ.pow_succ_reduce _
                (ℯ.pow_positivity _ (nat.lift.succ_pos ℝ _) _),

            have scaled_pow_ineq : 0 < (↑(2 ^ n) * ↑2 : ℝ),
                rw zero_is_lifted_zero_lemma ℕ ℝ,
                rw ← has_lift_mul_distributivity.eq,
                rw ← nat.pow_succ,
                refine has_lift_lt_preserved.lt
                    (lt_of_lt_of_le (nat.zero_lt_one) (nat.pow_two_ge_one _)),

            rw ExpLog.pow_domain_irrel _ ↑(2 ^ n.succ) _ _ scaled_pow_ineq _
                (by rw [nat.pow_succ, has_lift_mul_distributivity.eq]),

            rw ℯ.pow_homomorphism_mul _
                (lifted_pow2_pos _) _ (nat.lift.succ_pos ℝ _) _,

            rw hn,
    end

end term --——————————————————————————————————————————————————————————————————————————————--

/--
`ζ` Series Partial Sum for Real Inputs
-/
def partial.on_reals
    [has_same_lifted_zero nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    (ℯ : ExpLog ℝ ℝ)
    := partial_sum ∘ (term.on_reals ℯ)

/--
-/
def partial.on_reals.is_cauchy
    [has_add_le_add ℝ]
    [has_add_lt_add ℝ]

    [has_add_nonneg ℝ]
    [has_add_sub_assoc ℝ]
    [has_le_add_of_nonneg_of_le ℝ]
    [has_left_add_distributivity ℝ]
    [has_left_sub_distributivity ℝ]
    [has_lt_sub_neg ℝ]
    [has_mul_assoc ℝ]
    [has_pos_mul_neg_is_neg ℝ]
    [has_zero_right_add_cancel ℝ]
    [has_right_add_distributivity ℝ]

    [has_left_unit ℝ]
    [has_right_unit ℝ]

    [has_same_lifted_one nat ℝ]
    [has_same_lifted_zero nat ℝ]
    [has_lift_mul_distributivity nat ℝ]
    [has_lift_add_distributivity nat ℝ]
    [has_lift_lt_preserved nat ℝ]
    [has_lift_le_preserved ℕ ℝ]

    [has_sub_add_sub_cancel ℝ]
    [has_sub_cancel_to_zero ℝ]
    [has_sub_sub ℝ]
    [has_sub_ne_zero_of_ne ℝ]
    [has_zero_left_add_cancel ℝ]
    [has_zero_left_absorb ℝ]
    [has_zero_right_absorb ℝ]
    [has_inv_mul_right_cancel_self ℝ]
    [has_right_sub_distributivity ℝ]
    [has_add_sub_exchange ℝ]
    [has_inv_right_mul_lt_pos ℝ]
    [has_left_mul_inv_lt_neg ℝ]
    [has_zero_sub_is_neg ℝ]
    [has_inv_reverses_lt ℝ]
    [has_lt_pos_mul_preserves_right ℝ]
    [has_mul_pos ℝ]
    [has_sub_pos ℝ]

    (ℯ : ExpLog ℝ ℝ)

    (abs)
        (abs_zero abs_one abs_add abs_sub abs_mul abs_inv abs_ge_zero ge_zero_to_abs)

    (half ceil)

    (σ σ_gt_1)

    : is_cauchy abs (partial.on_reals ℯ σ) :=

    begin
        refine condensation.cauchy_test _ abs_zero abs_ge_zero abs_add ge_zero_to_abs _
            (term.on_reals.nonneg _ _)
            (term.on_reals.non_increasing _ _
                (lt_trans (nat.lift.zero_lt_one _) σ_gt_1)) _,

        rw funext (term.on_reals.rewrite.pow_reduction ℯ _),

        refine geometric.series.is_cauchy _
            abs_one abs_inv abs_sub abs_add abs_mul ge_zero_to_abs _ half ceil _ _
            (ExpLog.exp_lt_zero_is_lt_one _
                (has_pos_mul_neg_is_neg.lt
                    (ExpLog.log_gt_one_is_gt_zero _ (nat.lift.succ_pos ℝ _) _)
                    (has_lt_sub_neg.lt σ_gt_1))),

        rw one_is_lifted_one_lemma nat ℝ,

        refine has_lift_lt_preserved.lt (nat.lt_succ_self _),
    end

end riemann_zeta --——————————————————————————————————————————————————————————————————————--
