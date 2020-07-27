/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    cauchy.lean                                                       |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .exponential

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {α : Type*} {β : Type*}

section cauchy --————————————————————————————————————————————————————————————————————————--
variables [has_lt α] [has_zero α]

variables [has_sub β]

variables (abs : β → α)

variables (seq : nat → β)

/--
-/
structure is_cauchy.struct (ε : α) (εpos : 0 < ε)
    := (index       : nat)
       (boundedness : Π j, index ≤ j → abs (seq j - seq index) < ε)

/--
-/
def is_cauchy
    := Π ε εpos, is_cauchy.struct abs seq ε εpos

/--
-/
structure is_convergent.struct (ℓ : β) (ε : α) (εpos : 0 < ε)
    := (index       : nat)
       (boundedness : Π n, index ≤ n → abs (ℓ - seq n) < ε)

/--
-/
def is_convergent (ℓ)
    := Π ε εpos, is_convergent.struct abs seq ℓ ε εpos

/--
-/
structure CauchySequence
    := (sequence  : nat → β)
       (condition : is_cauchy abs sequence)

/--
-/
structure ConvergentSequence
    := (sequence  : nat → β)
       (limit     : β)
       (condition : is_convergent abs sequence limit)

end cauchy --————————————————————————————————————————————————————————————————————————————--

namespace is_cauchy --———————————————————————————————————————————————————————————————————--
variables [has_zero α]

/--
-/
def from_convergent
    [has_add α] [preorder α] [has_add_lt_add α]

    [has_sub β] [has_add β] [has_sub_add_sub_cancel β]

    (abs     : β → α)
    (abs_sub : Π x y, abs (x - y) = abs (y - x))
    (abs_add : Π x y, abs (x + y) ≤ abs x + abs y)

    (half : Half α)

    (seq ℓ)

    : is_convergent abs seq ℓ → is_cauchy abs seq :=

    begin
        intros convergence ε εpos,

        let cond := convergence _ (half.preserve_pos εpos),
        let i := cond.index,

        existsi i,

        intros _ le_j,

        rw ← has_sub_add_sub_cancel.eq _ ℓ _,

        refine lt_of_le_of_lt (abs_add _ _) _,

        rw abs_sub,
        rw ← half.doubled_inv ε,

        refine has_add_lt_add.lt
            (cond.boundedness _ le_j) (cond.boundedness _ (le_refl _)),
    end

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_sub α]

section closed_mul --————————————————————————————————————————————————————————————————————--
variables [has_lt α] [has_mul α] [has_inv α]

section closed_left_mul --———————————————————————————————————————————————————————————————--
variables [has_left_sub_distributivity α] [has_left_inv_pos_lt α]
          [has_mul_zero_is_zero α] [has_right_mul_inv_lt_pos α]

/--
-/
def closed.sequence_left_mul
    (abs     : α → α)
    (abs_mul : Π x y, abs (x * y) = abs x * abs y)

    (seq)

    (C absC_pos)

    : is_cauchy abs seq → is_cauchy abs (λ n, C * seq n) :=

    begin
        intros cauchy_condition ε εpos,

        let division := has_left_inv_pos_lt.lt absC_pos εpos,

        rw has_mul_zero_is_zero.eq at division,

        let cauchy := cauchy_condition _ division,

        existsi cauchy.index,
        intros _ le_j,

        rw ← has_left_sub_distributivity.eq,
        rw abs_mul,

        refine has_right_mul_inv_lt_pos.lt absC_pos (cauchy.boundedness _ le_j),
    end

/--
-/
def closed.partial_sum_left_mul
    [has_add α] [has_left_add_distributivity α]

    (abs abs_mul)

    (seq : nat → α)

    (C absC_pos)

    : is_cauchy abs (partial_sum seq) → is_cauchy abs (partial_sum (λ n, C * seq n)) :=

    begin
        rw partial_sum.left_mul_commute _ C,
        refine closed.sequence_left_mul _ abs_mul _ _ absC_pos,
    end

end closed_left_mul --———————————————————————————————————————————————————————————————————--

section closed_right_mul --——————————————————————————————————————————————————————————————--
variables [has_right_sub_distributivity α] [has_right_inv_pos_lt α]
          [has_zero_mul_is_zero α] [has_left_mul_inv_lt_pos α]

/--
-/
def closed.sequence_right_mul
    (abs     : α → α)
    (abs_mul : Π x y, abs (x * y) = abs x * abs y)

    (seq)

    (C absC_pos)

    : is_cauchy abs seq → is_cauchy abs (λ n, seq n * C) :=

    begin
        intros cauchy_condition ε εpos,

        let division := has_right_inv_pos_lt.lt absC_pos εpos,

        rw has_zero_mul_is_zero.eq at division,

        let cauchy := cauchy_condition _ division,

        existsi cauchy.index,
        intros _ le_j,

        rw ← has_right_sub_distributivity.eq,
        rw abs_mul,

        refine has_left_mul_inv_lt_pos.lt absC_pos (cauchy.boundedness _ le_j),
    end

/--
-/
def closed.partial_sum_right_mul
    [has_add α] [has_right_add_distributivity α]

    (abs abs_mul)

    (seq : nat → α)

    (C absC_pos)

    : is_cauchy abs (partial_sum seq) → is_cauchy abs (partial_sum (λ n, seq n * C)) :=

    begin
        rw partial_sum.right_mul_commute _ C,
        refine closed.sequence_right_mul _ abs_mul _ _ absC_pos,
    end

end closed_right_mul --——————————————————————————————————————————————————————————————————--

end closed_mul --————————————————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_add α]
          [has_sub_self_is_zero α] [has_add_sub_assoc α]

/--
-/
def closed.partial_sum_translate
    [has_lt α]
    (abs : α → α)
    (seq) (k)
    : is_cauchy abs (partial_sum (translate seq k)) → is_cauchy abs (partial_sum seq) :=
    begin
        intros cauchy_condition ε εpos,

        let cauchy := cauchy_condition _ εpos,

        existsi k + cauchy.index,

        intros _ le,

        let index_ineq := nat.le_sub_left_of_add_le le,

        rw partial_sum.sub_as_translate seq le,
        rw ← translate.combine,
        rw ← nat.sub_sub,
        rw ← partial_sum.sub_as_translate (translate seq _) index_ineq,

        refine cauchy.boundedness _ index_ineq,
    end

--———————————————————————————————————————————————————————————————————————————————————————--
variables [preorder α] [has_add_nonneg α]

section comparison --————————————————————————————————————————————————————————————————————--
variables [has_add_le_add α]

variables [has_zero β] [has_add β] [has_sub β]
          [has_add_sub_assoc β] [has_sub_self_is_zero β]

variables (abs            : α → α)
          (ge_zero_to_abs : Π z, 0 ≤ z → abs z = z)

variables (abs_βα         : β → α)
          (abs_βα_zero    : abs_βα 0 = 0)
          (abs_βα_add     : Π x y, abs_βα (x + y) ≤ abs_βα x + abs_βα y)
          (abs_βα_ge_zero : Π x, 0 ≤ abs_βα x)

include ge_zero_to_abs abs_βα abs_βα_zero abs_βα_add abs_βα_ge_zero

/--
-/
def comparison
    (a b) (le : abs_βα ∘ b ≤ a)

    : is_cauchy abs (partial_sum a) → is_cauchy abs_βα (partial_sum b) :=

    begin
        intros cauchy_condition ε εpos,

        let cauchy := cauchy_condition _ εpos,

        existsi cauchy.index,

        intros _ le_j,

        refine lt_of_le_of_lt _ (cauchy.boundedness _ le_j),

        rw partial_sum.sub_as_translate a le_j,
        rw partial_sum.sub_as_translate b le_j,
        rw triangle_equality abs ge_zero_to_abs _ _ _,

        refine le_trans
            (triangle_inequality _ abs_βα_zero abs_βα_add _ _)
            (partial_sum.monotonicity (translate.monotonicity le _) _),

        refine λ _, le_trans (abs_βα_ge_zero _) (le _),
    end

/--
-/
def closed.inclusion
    (seq)

    : is_cauchy abs (partial_sum (abs_βα ∘ seq)) → is_cauchy abs_βα (partial_sum seq) :=

    begin
        refine comparison _
            ge_zero_to_abs abs_βα abs_βα_zero abs_βα_add abs_βα_ge_zero _ _
            (λ _, le_refl _),
    end

end comparison --————————————————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_zero_right_add_cancel α] [has_add_le_add α] [has_le_sub_add_le α]
          [has_le_add_of_nonneg_of_le α]

/--
-/
def closed.subsequence_partial_sum.ineq
    (seq : nat → α)

    (nonneg φ sinc_φ i j)

    : i ≤ j → partial_sum (seq ∘ φ) j - partial_sum (seq ∘ φ) i
            ≤ partial_sum seq (φ j) - partial_sum seq (φ i) :=

    begin
        let strong_inc_φ := strictly_increasing.as_increasing_strong _ sinc_φ,

        intros i_le_j,

        rw partial_sum.sub_as_translate (seq ∘ φ) i_le_j,
        rw partial_sum.sub_as_translate seq (strong_inc_φ _ _ i_le_j),

        induction j with _ hj,
            cases i_le_j,
                rw [nat.sub_self, nat.sub_self, partial_sum, partial_sum],

            cases nat.of_le_succ i_le_j,
                rw nat.succ_sub h,

                refine le_trans
                    (has_add_le_add.le (le_refl _) (hj h)) (has_le_sub_add_le.le _),

                rw partial_sum.sub_as_translate
                    (translate seq _) (nat.sub_le_sub_right (le_of_lt (sinc_φ _)) _),

                rw translate.combine,
                rw nat.add_sub_of_le (strong_inc_φ _ _ h),
                rw nat.sub_sub_sub_cancel_right (strong_inc_φ _ _ h),
                rw translate,
                rw nat.add_sub_of_le h,

                refine le_trans _
                    (partial_sum.double_monotonicity _ 1 _ _
                        (translate.preserve_nonneg _ nonneg _)
                        (λ _, le_refl _) (nat.le_sub_left_of_add_le (sinc_φ _))),

                rw [partial_sum, partial_sum, translate],
                rw has_zero_right_add_cancel.eq,
                rw nat.add_zero,
                rw [h, nat.sub_self, partial_sum],

                refine partial_sum.preserve_nonneg _
                    (translate.preserve_nonneg _ nonneg _) _,
    end

/--
-/
def closed.subsequence_partial_sum
    (abs      : α → α)
    (abs_mono : Π x y, 0 ≤ x → x ≤ y → abs x ≤ abs y)

    (seq nonneg)

    (φ sinc_φ)

    : is_cauchy abs (partial_sum seq) → is_cauchy abs (partial_sum (seq ∘ φ)) :=

    begin
        intros cauchy_condition ε εpos,

        let ge_index := strictly_increasing.ge_index _ sinc_φ,
        let cauchy := cauchy_condition ε εpos,

        existsi cauchy.index,

        intros _ le_j,

        let strong_inc := strictly_increasing.as_increasing_strong _ sinc_φ _ _ le_j,

        refine lt_of_le_of_lt
            (le_trans
                (abs_mono _ _
                    (partial_sum.lower_differences.bottom _
                        (nonneg_compose_preserve _ _ nonneg) le_j)
                    (closed.subsequence_partial_sum.ineq _ nonneg _ sinc_φ _ _ le_j))
                (abs_mono _ _
                    (partial_sum.lower_differences.bottom _ nonneg strong_inc)
                    (partial_sum.lower_differences _ nonneg (ge_index _) strong_inc)))
            (cauchy.boundedness _ (le_trans le_j (ge_index _))),
    end

/--
-/
def closed.scaled_sequence_partial_sum
    (abs : α → α)
    (abs_mono)

    (seq nonneg)

    (N Npos)

    : is_cauchy abs (partial_sum seq) → is_cauchy abs (partial_sum (λ n, seq (N * n)))

    := closed.subsequence_partial_sum _
        abs_mono _ nonneg _ (λ _, nat.lt_add_of_pos_right Npos)

end is_cauchy --—————————————————————————————————————————————————————————————————————————--

namespace condensation --————————————————————————————————————————————————————————————————--
variables [preorder α] [has_zero α] [has_one α] [has_sub α] [has_add α] [has_mul α]
          [has_sub_self_is_zero α] [has_add_sub_assoc α]
          [has_sub_add_sub_cancel α] [has_add_nonneg α] [has_add_le_add α]
          [has_le_add_of_nonneg_of_le α]

/--
-/
def shape_sum_comparison
    (abs            : α → α)
    (ge_zero_to_abs : Π z, 0 ≤ z → abs z = z)

    (seq nonneg)

    (φ sinc_φ)

    : is_cauchy abs (partial_sum (shape_sum seq φ))
    → is_cauchy abs (partial_sum (translate seq (φ 0))) :=

    begin
        intros cauchy_condition ε εpos,

        let translate_nonneg := translate.preserve_nonneg _ nonneg _,
        let strong_inc       := strictly_increasing.as_increasing_strong _ sinc_φ,
        let cauchy           := cauchy_condition _ εpos,

        existsi φ cauchy.index - φ 0,

        intros _ le_j,

        let I_le_ju0
            := le_trans
                (strictly_increasing.ge_index _ sinc_φ _)
                (nat.le_add_of_sub_le_right le_j),

        rw partial_sum.sub_as_translate (translate seq _) le_j,
        rw translate.combine,
        rw nat.add_sub_of_le (strong_inc _ _ (nat.zero_le _)),
        rw nat.neg_right_swap (strong_inc _ _ (nat.zero_le _)),
        rw triangle_equality abs ge_zero_to_abs _ translate_nonneg _,

        let condition := cauchy.boundedness _ I_le_ju0,

        rw partial_sum.sub_as_translate (shape_sum seq _) I_le_ju0   at condition,
        rw shape_sum.unfold seq _ sinc_φ I_le_ju0                    at condition,
        rw triangle_equality abs ge_zero_to_abs _ translate_nonneg _ at condition,

        refine lt_of_le_of_lt
            (partial_sum.index_monotonicity _ translate_nonneg
                (nat.sub_le_sub_right (strictly_increasing.ge_index _ sinc_φ _) _))
            condition,
    end

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_lift_t nat α] [has_lift_zero_same nat α] [has_lift_one_same nat α]
          [has_lift_add_comm nat α] [has_zero_mul_is_zero α] [has_left_unit α]
          [has_right_add_distributivity α]

variables (abs            : α → α)
          (abs_zero       : abs 0 = 0)
          (abs_ge_zero    : Π x, 0 ≤ abs x)
          (abs_add        : Π x y, abs (x + y) ≤ abs x + abs y)
          (ge_zero_to_abs : Π z, 0 ≤ z → abs z = z)

variables (seq     : nat → α)
          (nonneg  : 0 ≤ seq)
          (non_inc : non_increasing seq)

include abs abs_zero abs_ge_zero abs_add ge_zero_to_abs seq nonneg non_inc

/--
-/
def cauchy_schlomilch_test
    (φ) (sinc_φ : strictly_increasing φ)

    : is_cauchy abs (partial_sum (λ n, ↑(nat.successive_difference φ n) * seq (φ n)))
    → is_cauchy abs (partial_sum seq) :=

    begin
        intros cauchy,

        let comparison
            := is_cauchy.comparison _
                ge_zero_to_abs abs abs_zero abs_add abs_ge_zero _ _ _,

        refine is_cauchy.closed.partial_sum_translate _ _ _
            (shape_sum_comparison _ ge_zero_to_abs _ nonneg _ sinc_φ (comparison cauchy)),

        intros _,

        rw function.comp_app,
        rw shape_sum,
        rw partial_sum.sub_as_translate seq (le_of_lt (sinc_φ _)),
        rw partial_sum.from_mul,

        refine le_trans
            (triangle_inequality _ abs_zero abs_add _ _) (partial_sum.monotonicity _ _),

        intros _,

        rw function.comp_app,
        rw translate,
        rw ge_zero_to_abs _ (nonneg _),

        refine non_increasing.as_non_increasing_strong _ non_inc _ _,
    end

/--
-/
def cauchy_test
    : is_cauchy abs (partial_sum (λ n, ↑(2 ^ n) * seq (2 ^ n - 1)))
    → is_cauchy abs (partial_sum seq) :=

    begin
        let result
            := cauchy_schlomilch_test _
                abs_zero abs_ge_zero abs_add ge_zero_to_abs _ nonneg non_inc _ _,

        rw (_ : nat.successive_difference (λ n, 2 ^ n - 1) = pow 2) at result,

        refine result,
        refine funext _,

        intros _,

        rw nat.successive_difference,
        rw nat.sub_sub,
        rw ← nat.add_sub_assoc (nat.pow_two_ge_one _),
        rw nat.add_sub_cancel_left,
        rw (nat.sub_eq_iff_eq_add _).2 _,

        refine nat.le_add_left _ _,
        refine nat.mul_two _,

        intros _,

        refine nat.sub_mono_left_strict (nat.pow_two_ge_one _) (nat.pow_two_monotonic _),
    end

end condensation --——————————————————————————————————————————————————————————————————————--

namespace geometric --———————————————————————————————————————————————————————————————————--
variables [has_zero α] [has_one α] [has_add α] [has_mul α] [has_sub α] [has_inv α]
          [has_mul_assoc α] [has_zero_right_add_cancel α] [has_right_unit α]
          [has_sub_ne_zero_of_ne α] [has_right_sub_distributivity α]
          [has_sub_self_is_zero α] [has_inv_mul_right_cancel_self α]
          [has_left_sub_distributivity α] [has_add_sub_exchange α]
          [has_right_add_distributivity α]

section series_definitions --————————————————————————————————————————————————————————————--
local notation a `^` n := nat.power a n

/--
-/
def series.formula
    (x : α) (x_ne_1 : x ≠ 1)

    (n)

    : partial_sum (nat.power x) n = (1 - x ^ n) * (1 - x)⁻¹ :=

    begin
        induction n with n hn,
            rw partial_sum,
            rw nat.power,
            rw has_right_sub_distributivity.eq,
            rw has_sub_self_is_zero.eq,

            rw partial_sum,
            rw nat.power,
            rw hn,

            rw (_ : x ^ n                       + (1 - x ^ n) * (1 - x)⁻¹
                  = x ^ n * (1 - x) * (1 - x)⁻¹ + (1 - x ^ n) * (1 - x)⁻¹),

            rw ← has_right_add_distributivity.eq,
            rw has_left_sub_distributivity.eq,
            rw has_right_unit.eq,
            rw has_add_sub_exchange.eq,
            rw has_sub_self_is_zero.eq,
            rw has_zero_right_add_cancel.eq,
            rw has_mul_assoc.eq,
            rw has_inv_mul_right_cancel_self.eq _
                (has_sub_ne_zero_of_ne.ne x_ne_1.symm),

            rw has_right_unit.eq,
    end

end series_definitions --————————————————————————————————————————————————————————————————--

section series_is_cauchy --——————————————————————————————————————————————————————————————--

/--
-/
def series.is_cauchy
    [has_lift_t nat α]
    [has_lift_add_comm nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]

    [preorder α]
    [has_add_lt_add α]
    [has_left_add_distributivity α]
    [has_sub_add_sub_cancel α]
    [has_sub_sub α]
    [has_mul_zero_is_zero α]
    [has_left_unit α]
    [has_inv_right_mul_lt_pos α]
    [has_left_mul_inv_lt_neg α]
    [has_zero_left_add_cancel α]
    [has_zero_lt_one α]
    [has_mul_pos α]
    [has_sub_pos α]

    (abs            : α → α)
    (abs_one        : abs 1 = 1)
    (abs_inv        : Π a, abs (a⁻¹) = (abs a)⁻¹)
    (abs_sub        : Π x y, abs (x - y) = abs (y - x))
    (abs_add        : Π x y, abs (x + y) ≤ abs x + abs y)
    (abs_mul        : Π x y, abs (x * y) = abs x * abs y)
    (ge_zero_to_abs : Π a, 0 ≤ a → abs a = a)

    (ℯ : ExpLog α α)

    (half : Half α)

    (ceil : LiftCeil α)

    (x : α) (xpos : 0 < x) (x_lt_one : x < 1)

    : is_cauchy abs (partial_sum (ℯ.nat_pow x xpos)) :=

    begin
        refine is_cauchy.from_convergent abs abs_sub abs_add half _ (1 - x)⁻¹ _,

        intros ε εpos,

        have abs_x_pos : 0 < abs x,
            rw ge_zero_to_abs _ (le_of_lt xpos),
            refine xpos,

        have abs_x_lt_one : abs x < 1,
            rw ge_zero_to_abs _ (le_of_lt xpos),
            refine x_lt_one,

        let one_minus_x_pos
            := has_sub_pos.lt x_lt_one,

        let ε_mul_one_minus_x
            := has_mul_pos.lt εpos one_minus_x_pos,

        existsi (ceil.map (ℯ.log _ ε_mul_one_minus_x * (ℯ.log _ abs_x_pos)⁻¹)).succ,

        intros n le_n,

        rw ← ℯ.nat_pow_to_nat_power,
        rw series.formula _ (ne_of_lt x_lt_one),
        rw has_right_sub_distributivity.eq,
        rw has_left_unit.eq,
        rw has_sub_sub.eq,
        rw has_sub_self_is_zero.eq,
        rw has_zero_left_add_cancel.eq,
        rw abs_mul,
        rw abs_inv,
        rw ge_zero_to_abs _ (le_of_lt one_minus_x_pos),
        rw nat.power.mul_commute _ abs_one abs_mul,

        refine has_inv_right_mul_lt_pos.lt one_minus_x_pos _,

        rw ℯ.nat_pow_to_nat_power,
        rw ← ℯ.log_inverted _ ε_mul_one_minus_x,

        refine ℯ.exp_monotonic (has_left_mul_inv_lt_neg.lt
           (ℯ.log_lt_one_is_lt_zero abs_x_pos abs_x_lt_one) (ceil.lift_lt le_n)),
    end

end series_is_cauchy --——————————————————————————————————————————————————————————————————--

end geometric --—————————————————————————————————————————————————————————————————————————--
