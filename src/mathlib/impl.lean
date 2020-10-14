/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis/mathlib                                        |
| @file:    mathlib/impl.lean                                                 |
| @authors: Brandon H. Gomes, Alex Kontorovich                                |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import analysis.special_functions.exp_log
import topology.metric_space.cau_seq_filter

import riemann_hypothesis

/-!
-/

open riemann_hypothesis
open_locale big_operators

noncomputable theory

/--
-/
instance : Algebra ℝ := {
    zero := has_zero.zero,
    one := has_one.one,
    neg := has_neg.neg,
    add := has_add.add,
    sub := has_sub.sub,
    mul := has_mul.mul,
    inv := has_inv.inv
}

/--
-/
instance : Algebra ℂ := {
    zero := has_zero.zero,
    one := has_one.one,
    neg := has_neg.neg,
    add := has_add.add,
    sub := has_sub.sub,
    mul := has_mul.mul,
    inv := has_inv.inv
}

/--
-/
def real_explog : ExpLog ℝ ℝ :=
{
    exp                   := real.exp,
    exp_homomorphism_zero := real.exp_zero,
    exp_homomorphism      := real.exp_add,
    exp_homomorphism_inv  := λ _ _, by rw [real.exp_sub, division_def],
    exp_injective         := λ _ _ eq, real.exp_injective eq,
    exp_monotonic         := λ _ _ lt, real.exp_lt_exp.mpr lt,
    exp_monotonic_reverse := λ _ _ lt, real.exp_lt_exp.mp lt,
    exp_positive          := real.exp_pos,
    log                   := λ a _, real.log a,
    log_domain_irrel      := λ _ _ _ _ eq, by rw eq,
    log_inverted          := λ _ apos, by rw real.exp_log apos,
}

/--
-/
def complex_witness.proofs.abs_exp_is_exp_real_part
    : Π z, complex.abs (complex.exp z) = real.exp (complex.re z) :=
begin
    intros,
    rw [← complex.exp_of_real_re,
          complex.abs_exp_eq_iff_re_eq.mpr,
        ← complex.of_real_exp,
          complex.abs_of_real,
          abs_of_pos (real.exp_pos _)],
    repeat { refine rfl },
end

/--
-/
def lim_le (f : cau_seq ℝ abs) (g : cau_seq ℝ abs)
    : (∃ j, ∀ i, j ≤ i → f i ≤ g i) → f.lim ≤ g.lim :=
begin
  intros,
  refine le_of_tendsto_of_tendsto (cau_seq.tendsto_limit _) (cau_seq.tendsto_limit _) _,
  rwa [filter.eventually_le, filter.eventually_at_top],
end

/--
-/
def unit_circle_pow_lemma
    : Π x, complex.abs x ≤ 1 → Π (n : ℕ), complex.abs (x ^ n) ≤ 1 :=
begin
    intros _ x_le_1 _,
    induction n with n hn,
        simp,
        rw pow_succ,
        refine le_trans _ hn,
        rw is_absolute_value.abv_pow complex.abs,
        rw complex.abs_mul,
        rw (_ : complex.abs x ^ n = 1 * complex.abs x ^ n),
        refine mul_le_mul
            x_le_1 (le_of_eq (is_absolute_value.abv_pow _ _ _)) (complex.abs_nonneg _) zero_le_one,
        simp,
end

/--
-/
def complex_witness.proofs.exp_linearization
    : Π x, complex.abs x ≤ 1
    → Π z, complex.abs (complex.exp (x * z) - (x * z + 1))
        ≤ (complex.abs x * complex.abs x) * real.exp (complex.abs z) :=
begin
    intros _ x_le_1 _,
    rw complex.exp,
    rw ← cau_seq.lim_const (x*z+1),
    rw sub_eq_add_neg,
    rw ← cau_seq.lim_neg,
    rw cau_seq.lim_add,
    rw ← complex.lim_abs,
    rw real.exp,
    rw complex.exp,
    rw ← complex.lim_re,
    rw ← cau_seq.lim_const ((complex.abs x) * (complex.abs x)),
    rw cau_seq.lim_mul_lim,
    rw mul_comm (cau_seq.const _ _),

    refine lim_le _ _ _,
    existsi 2,
    intros i i_ge_2,

    rw (complex.cau_seq_re _).mul_apply,

    rw (_ : (complex.cau_seq_re (complex.exp' ↑(complex.abs z))) i
          = (∑ k in finset.range i, ((complex.abs z) : ℂ) ^ k / k.fact).re),

    rw ← (finset.range _).sum_hom complex.re,
    norm_cast,

    show complex.abs (∑ k in finset.range i, (x * z) ^ k / k.fact - (x * z + 1))
            ≤ (∑ k in finset.range i, (complex.abs z) ^ k / k.fact) * (complex.abs x * complex.abs x),

    rw (_ : (x * z + 1) = ∑ k in finset.range 2, (x * z) ^ k / ↑(k.fact)),

    rw sum_range_sub_sum_range i_ge_2,

    rw (_ : complex.abs (∑ k in (finset.range i).filter (λ k, 2 ≤ k), (x * z) ^ k / ↑(k.fact))
          = complex.abs (∑ k in (finset.range i).filter (λ k, 2 ≤ k), x ^ 2 * x ^ (k - 2) * z ^ k / ↑(k.fact))),

    rw (_ : (∑ k in finset.range i, complex.abs z ^ k / ↑(k.fact))
          = (∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + (1 + complex.abs z))),

    rw (_ : (∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + (1 + complex.abs z))
          * (complex.abs x * complex.abs x)
          = complex.abs x ^ 2
          * (∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + (1 + complex.abs z))),

    have drop_extra_powers_of_x
        : complex.abs (∑ k in (finset.range i).filter (λ k, 2 ≤ k), x ^ 2 * x ^ (k - 2) * z ^ k / ↑(k.fact))
        ≤ ∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs x ^ 2 * (complex.abs z ^ k / ↑(k.fact)),
    {
        refine le_trans (abv_sum_le_sum_abv _ _) (finset.sum_le_sum (λ m _, _)),

        rw mul_div_assoc,
        rw complex.abs_mul,
        rw complex.abs_mul,
        rw is_absolute_value.abv_pow complex.abs,
        rw complex.abs_div,
        rw complex.abs_cast_nat,
        rw ← mul_div_assoc,
        rw division_def,
        rw division_def,
        rw ← is_absolute_value.abv_pow complex.abs z,
        rw ← mul_assoc,

        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right _ (complex.abs_nonneg _)) (by simp),

        have : complex.abs x ^ 2 * complex.abs (x ^ (m - 2)) ≤ complex.abs x ^ 2 * 1,
            by refine mul_le_mul_of_nonneg_left (unit_circle_pow_lemma _ x_le_1 _) (pow_nonneg (complex.abs_nonneg _) _),

        simp at this,
        refine this,
    },

    simp [abs_mul, is_absolute_value.abv_pow complex.abs, complex.abs_div, finset.mul_sum.symm]
        at drop_extra_powers_of_x,

    refine le_trans drop_extra_powers_of_x (mul_le_mul (le_refl _) _ _ (pow_nonneg (complex.abs_nonneg _) _)),

    rw (_ : ∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact)
          = ∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + 0),

    rw (_ : ∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + 0 + (1 + complex.abs z)
          = ∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact) + (1 + complex.abs z)),

    refine add_le_add_left _ (∑ k in (finset.range i).filter (λ k, 2 ≤ k), complex.abs z ^ k / ↑(k.fact)),
    rw (_ : (0 : ℝ) = 0 + 0),
    refine add_le_add (by linarith) (complex.abs_nonneg _),
    simp,
    simp,
    simp,
    rw (_ : (0 : ℝ) = ∑ k in (finset.range i).filter (λ k, 2 ≤ k), 0),
    refine finset.sum_le_sum _,
    intros m _,
    rw (_ : complex.abs z ^ m / (m.fact : ℝ) = complex.abs z ^ m * (1 / (m.fact : ℝ))),
    refine mul_nonneg _ _,
    rw ← is_absolute_value.abv_pow complex.abs,
    refine complex.abs_nonneg _,
    refine le_of_lt (one_div_pos.mpr _),
    norm_cast,
    refine nat.fact_pos _,
    ring,
    refine (finset.sum_eq_zero _).symm,
    intros,
    refine rfl,
    ring,
    rw (_ : (1 + complex.abs z) = ∑ k in finset.range 2, (complex.abs z) ^ k / ↑(k.fact)),
    rw ← sum_range_sub_sum_range i_ge_2,
    simp,
    simp [sub_eq_add_neg, finset.sum_range_succ, add_assoc],
    ring,
    refine congr_arg complex.abs _,
    refine finset.sum_congr rfl _,
    intros,
    rw mul_pow,
    rw ← pow_add,
    rw nat.add_sub_cancel',
    simp at H,
    refine H.2,
    simp [sub_eq_add_neg, finset.sum_range_succ, add_assoc],
    refine rfl,
end

/--
-/
def complex_witness.proofs.real_log_bound
    : Π (x : ℝ) (p : 0 < 1 - x),
        complex.abs ↑x ≤ 2⁻¹ → complex.abs ↑(real.log (1 - x)) ≤ complex.abs ↑x + complex.abs ↑x :=
begin
    intros _ _ x_le_half,
    rw complex.abs_of_real at x_le_half,
    simp,

    have ineq0 : abs (∑ i in finset.range 0, x ^ (i + 1) / (↑i + 1) + real.log (1 - x))
               ≤ abs x ^ (0 + 1) / (1 - abs x),
    {
        refine real.abs_log_sub_add_sum_range_le _ _,
        rw (_ : (2 : ℝ)⁻¹ = 1 / 2) at x_le_half,
        linarith,
        simp,
    },
    simp at ineq0,

    rw (_: abs x + abs x = abs x / (1 - 2⁻¹)),

    have ineq1 : -(2⁻¹) ≤ -(abs x),
        by refine neg_le_neg x_le_half,

    have ineq2 : 1 - 2⁻¹ ≤ 1 - abs x,
        by refine sub_le_sub_left x_le_half _,

    have ineq3 : (1 - abs x)⁻¹ ≤ (1 - 2⁻¹)⁻¹,
    {
        refine inv_le_inv_of_le _ _,
        simp,
        rw (_ : (2 : ℝ)⁻¹ = 1 / 2),
        linarith,
        simp,
        refine ineq2,
    },

    have ineq4 : abs x / (1 - abs x) ≤ abs x / (1 - 2⁻¹) ,
    {
        rw (_ : abs x / (1 - abs x) = (1 - abs x)⁻¹ * abs x),
        rw (_ : abs x / (1 - 2⁻¹) = (1 - 2⁻¹)⁻¹ * abs x),
        refine mul_le_mul ineq3 _ _ _,
        refine le_refl _,
        refine abs_nonneg _,
        rw (_: (1 - (2 : ℝ)⁻¹)⁻¹ = 2),
        linarith,
        ring,
        ring,
        ring,
    },

    linarith,
    ring,
end

/--
-/
def complex_witness : Complex ℂ ℝ :=
{
    real_part                := complex.re,
    abs                      := complex.abs,
    exp                      := complex.exp,
    real_explog              := real_explog,
    abs_nonneg               := complex.abs_nonneg,
    exp_nonzero              := complex.exp_ne_zero,
    exp_homomorphism_zero    := complex.exp_zero,
    exp_homomorphism         := complex.exp_add,
    exp_homomorphism_inv     := λ _ _, by rw [complex.exp_sub, division_def],
    real_part_scaling        := λ _ _, by rw [complex.mul_re, complex.of_real_im, complex.of_real_re, zero_mul, sub_zero],
    abs_exp_is_exp_real_part := complex_witness.proofs.abs_exp_is_exp_real_part,
    exp_linearization        := complex_witness.proofs.exp_linearization,
    real_log_bound           := complex_witness.proofs.real_log_bound
}
