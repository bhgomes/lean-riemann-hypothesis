/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    exponential.lean                                                  |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

import .basic

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables (α : Type*) (β : Type*)
variables [has_lt α] [has_zero α] [has_one α] [has_mul α] [has_inv α]
          [has_lt β] [has_zero β] [has_add β] [has_sub β]

/--
-/
structure ExpLog
    := (exp                   : β → α)
       (exp_homomorphism_zero : exp 0 = 1)
       (exp_homomorphism      : Π (x y), exp (x + y) = exp x * exp y)
       (exp_homomorphism_inv  : Π (x y), exp (x - y) = exp x * (exp y)⁻¹)
       (exp_injective         : Π {x y}, exp x = exp y → x = y)
       (exp_monotonic         : Π {x y}, x < y → exp x < exp y)
       (exp_monotonic_reverse : Π {x y}, exp x < exp y → x < y)
       (exp_positive          : Π b, 0 < exp b)
       (log                   : Π a : α, 0 < a → β)
       (log_domain_irrel      : Π x xpos y ypos, x = y → log x xpos = log y ypos)
       (log_inverted          : Π a apos, exp (log a apos) = a)

namespace ExpLog --——————————————————————————————————————————————————————————————————————--
variables {α β}

/--
-/
def log_homomorphism_zero
    [has_zero_lt_one α]
    (ℯ : ExpLog α β)
    : ℯ.log 1 has_zero_lt_one.lt = 0 :=
    begin
        refine ℯ.exp_injective _,
        rw exp_homomorphism_zero,
        rw ℯ.log_inverted _ has_zero_lt_one.lt,
    end

/--
-/
def log_homomorphism
    [has_mul_pos α]
    (ℯ : ExpLog α β)
    {x y}
    (xpos ypos)
    : ℯ.log (x * y) (has_mul_pos.lt xpos ypos)
    = ℯ.log x xpos + ℯ.log y ypos :=
    begin
        refine ℯ.exp_injective _,
        rw exp_homomorphism,
        rw [ℯ.log_inverted, ℯ.log_inverted, ℯ.log_inverted],
    end

/--
-/
def log_homomorphism_inv
    [has_mul_pos α]
    [has_inv_pos α]
    (ℯ : ExpLog α β)
    {x y}
    (xpos ypos)
    : ℯ.log (x * y⁻¹) (has_mul_pos.lt xpos (has_inv_pos.lt ypos))
    = ℯ.log x xpos - ℯ.log y ypos :=
    begin
        refine ℯ.exp_injective _,
        rw exp_homomorphism_inv,
        rw [ℯ.log_inverted, ℯ.log_inverted, ℯ.log_inverted],
    end

/--
-/
def log_monotonic
    (ℯ : ExpLog α β)
    {x y}
    (xpos ypos)
    : x < y → ℯ.log x xpos < ℯ.log y ypos :=
    begin
        intros x_lt_y,
        rw [← ℯ.log_inverted _ xpos, ← ℯ.log_inverted _ ypos] at x_lt_y,
        refine exp_monotonic_reverse _ x_lt_y,
    end

/--
-/
def log_monotonic_reverse
    (ℯ : ExpLog α β)
    {x y}
    (xpos ypos)
    : ℯ.log x xpos < ℯ.log y ypos → x < y :=
    begin
        intros logx_lt_logy,
        rw [← ℯ.log_inverted _ xpos, ← ℯ.log_inverted _ ypos],
        refine exp_monotonic _ logx_lt_logy,
    end

/--
-/
def log_lt_one_is_lt_zero
    [has_zero_lt_one α]
    (ℯ : ExpLog α β)
    {a}
    (apos)
    : a < 1 → ℯ.log a apos < 0 :=
    begin
        intros a_lt_1,
        rw ← ℯ.log_homomorphism_zero,
        refine ℯ.log_monotonic _ _ a_lt_1,
    end

/--
-/
def log_gt_one_is_gt_zero
    [has_zero_lt_one α]
    (ℯ : ExpLog α β)
    {a}
    (apos)
    : a > 1 → ℯ.log a apos > 0 :=
    begin
        intros a_gt_1,
        rw ← ℯ.log_homomorphism_zero,
        refine ℯ.log_monotonic _ _ a_gt_1,
    end

/--
-/
def exp_lt_zero_is_lt_one
    (ℯ : ExpLog α β)
    {b}
    : b < 0 → ℯ.exp b < 1 :=
    begin
        intros b_lt_0,
        rw ← ℯ.exp_homomorphism_zero,
        refine ℯ.exp_monotonic b_lt_0,
    end

/--
-/
def exp_gt_zero_is_gt_one
    (ℯ : ExpLog α β)
    {x}
    : x > 0 → ℯ.exp x > 1 :=
    begin
        intros b_gt_0,
        rw ← ℯ.exp_homomorphism_zero,
        refine ℯ.exp_monotonic b_gt_0,
    end

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_mul β]

/--
-/
def pow
    (ℯ : ExpLog α β)
    (a apos)
    (b)
    := ℯ.exp (ℯ.log a apos * b)

/--
-/
def pow_domain_irrel
    (ℯ : ExpLog α β)
    (x xpos)
    (y ypos)
    (b)
    : x = y → ℯ.pow x xpos b = ℯ.pow y ypos b :=
    begin
        intros x_eq_y,
        rw [pow, pow],
        rw log_domain_irrel _ _ _ _ _ x_eq_y,
    end

/--
-/
def pow_homomorphism_zero
    [has_mul_zero_is_zero β]
    (ℯ : ExpLog α β)
    (a apos)
    : ℯ.pow a apos 0 = 1 :=
    begin
        rw pow,
        rw has_mul_zero_is_zero.eq,
        rw exp_homomorphism_zero,
    end

/--
-/
def pow_homomorphism
    [has_left_add_distributivity β]
    (ℯ : ExpLog α β)
    (a apos x y)
    : ℯ.pow a apos (x + y) = ℯ.pow a apos x * ℯ.pow a apos y :=
    begin
        rw pow,
        rw has_left_add_distributivity.eq,
        rw exp_homomorphism,
        rw [← pow, ← pow],
    end

/--
-/
def pow_homomorphism_mul
    [has_mul_pos α]
    [has_right_add_distributivity β]
    (ℯ : ExpLog α β)
    (x xpos y ypos b)
    : ℯ.pow (x * y) (has_mul_pos.lt xpos ypos) b = ℯ.pow x xpos b * ℯ.pow y ypos b :=
    begin
        rw pow,
        rw log_homomorphism,
        rw has_right_add_distributivity.eq,
        rw exp_homomorphism,
        rw [← pow, ← pow],
    end

/--
-/
def pow_homomorphism_inv
    [has_left_sub_distributivity β]
    (ℯ : ExpLog α β)
    (a apos x y)
    : ℯ.pow a apos (x - y) = ℯ.pow a apos x * (ℯ.pow a apos y)⁻¹ :=
    begin
        rw pow,
        rw has_left_sub_distributivity.eq,
        rw exp_homomorphism_inv,
        rw [← pow, ← pow],
    end

/--
-/
def pow_id_at_one
    [has_one β]
    [has_right_unit β]
    (ℯ : ExpLog α β)
    (a apos)
    : ℯ.pow a apos 1 = a :=
    begin
        rw pow,
        rw has_right_unit.eq,
        rw log_inverted,
    end

/--
-/
def pow_homomorphism_one
    [has_zero_lt_one α]
    [has_zero_mul_is_zero β]
    (ℯ : ExpLog α β)
    (b)
    : ℯ.pow 1 has_zero_lt_one.lt b = 1 :=
    begin
        rw pow,
        rw log_homomorphism_zero,
        rw has_zero_mul_is_zero.eq,
        rw exp_homomorphism_zero,
    end

/--
-/
def pow_positivity
    (ℯ : ExpLog α β)
    (a apos b)
    : 0 < ℯ.pow a apos b
    := exp_positive _ _

/--
-/
def pow_neg_exponent_inverts
    [has_one β]
    [has_left_sub_distributivity β]
    [has_mul_zero_is_zero β]
    [has_left_unit α]
    (ℯ : ExpLog α β)
    (a apos b)
    : ℯ.pow a apos (0 - b) = (ℯ.pow a apos b)⁻¹ :=
    begin
        rw pow_homomorphism_inv,
        rw pow_homomorphism_zero,
        rw has_left_unit.eq,
    end

/--
-/
def pow_homomorphism_inv_from_neg
    [has_one β]
    [has_neg β]
    [has_zero_sub_is_neg β]
    [has_left_sub_distributivity β]
    [has_mul_zero_is_zero β]
    [has_left_unit α]
    (ℯ : ExpLog α β)
    (a apos x y)
    : ℯ.pow a apos x * ℯ.pow a apos (-y) = ℯ.pow a apos (x - y) :=
    begin
        rw ← has_zero_sub_is_neg.eq,
        rw pow_neg_exponent_inverts,
        rw ← pow_homomorphism_inv,
    end

/--
-/
def pow_succ_reduce
    [has_lift_t nat β]
    [has_one β]
    [has_right_unit β]
    [has_left_add_distributivity β]
    [has_lift_add_comm nat β]
    [has_lift_one_same nat β]
    (ℯ : ExpLog α β)
    (a apos)
    (n : nat)
    : ℯ.pow a apos ↑n.succ = ℯ.pow a apos ↑n * a :=
    begin
        rw ← nat.add_one,
        rw has_lift_add_comm.eq,
        rw pow_homomorphism,
        rw has_lift_one_same.eq,
        rw pow_id_at_one,
    end

/--
-/
def pow_monotonic
    [has_lt_pos_mul_preserves_right β]
    (ℯ : ExpLog α β)
    {x y}
    (xpos ypos)
    {b}
    (bpos)
    : x < y → ℯ.pow x xpos b < ℯ.pow y ypos b :=
    begin
        intros x_lt_y,
        refine exp_monotonic _
            (has_lt_pos_mul_preserves_right.lt bpos (log_monotonic _ _ _ x_lt_y)),
    end

/--
-/
def nat_pow
    [has_lift_t nat β]
    (ℯ : ExpLog α β)
    (a apos)
    (n : nat)
    := ℯ.pow a apos ↑n

/--
-/
def nat_pow_to_nat_power
    [has_one β]
    [has_right_unit β]
    [has_mul_zero_is_zero β]
    [has_left_add_distributivity β]
    [has_lift_t nat β]
    [has_lift_zero_same nat β]
    [has_lift_one_same nat β]
    [has_lift_add_comm nat β]
    (ℯ : ExpLog α β)
    (a : α) (apos : 0 < a)
    : nat.power a = ℯ.nat_pow a apos :=
    begin
        refine funext _,
        intros n,
        induction n with n hn,
            rw nat.power,
            rw nat_pow,
            rw has_lift_zero_same.eq,
            rw pow_homomorphism_zero,
            rw nat.power,
            rw nat.succ_eq_add_one,
            rw nat_pow,
            rw has_lift_add_comm.eq,
            rw pow_homomorphism,
            rw has_lift_one_same.eq,
            rw pow_id_at_one,
            rw hn,
            rw nat_pow,
    end

end ExpLog --————————————————————————————————————————————————————————————————————————————--
