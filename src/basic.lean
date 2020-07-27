/- ------------------------------------------------------------------------- -|
| @project: riemann_hypothesis                                                |
| @file:    basic.lean                                                        |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
|- ------------------------------------------------------------------------- -/

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {α : Type*} {β : Type*}

/--
-/
def const (b : β)
    := λ _ : α, b
notation `↓`:max b:max := const b

section pointwise_classes --—————————————————————————————————————————————————————————————--

/--
-/
instance pointwise.has_le [has_le β] : has_le (α → β)
    := ⟨λ f g, Π x, f x ≤ g x⟩

/--
-/
instance pointwise.has_zero [has_zero β] : has_zero (α → β)
    := ⟨↓0⟩

end pointwise_classes --—————————————————————————————————————————————————————————————————--

section algebra --———————————————————————————————————————————————————————————————————————--
variables (α) (β)

/--
provable from DD axioms
-/
class has_left_add_distributivity [has_add α] [has_mul α]
    := (eq : Π x y z : α, x * (y + z) = x * y + x * z)

/--
provable from DD axioms
-/
class has_right_add_distributivity [has_add α] [has_mul α]
    := (eq : Π x y z : α, (y + z) * x = y * x + z * x)

/--
AXIOM
-/
class has_left_sub_distributivity [has_sub α] [has_mul α]
    := (eq : Π x y z : α, x * (y - z) = x * y - x * z)

/--
AXIOM
-/
class has_right_sub_distributivity [has_sub α] [has_mul α]
    := (eq : Π x y z : α, (y - z) * x = y * x - z * x)

/--
-/
class has_lift_add_comm [has_lift_t α β] [has_add α] [has_add β]
    := (eq : Π x y : α, (↑(x + y) : β) = ↑x + ↑y)

/--
-/
class has_lift_sub_comm [has_lift_t α β] [has_sub α] [has_sub β]
    := (eq : Π x y : α, (↑(x - y) : β) = ↑x - ↑y)

/--
-/
class has_lift_mul_comm [has_lift_t α β] [has_mul α] [has_mul β]
    := (eq : Π x y : α, (↑(x * y) : β) = ↑x * ↑y)

/--
-/
class has_lift_inv_comm [has_lift_t α β] [has_inv α] [has_inv β]
    := (eq : Π a : α, (↑(a⁻¹) : β) = (↑a)⁻¹)

/--
AXIOM
-/
class has_right_unit [has_one α] [has_mul α]
    := (eq : Π a : α, a * 1 = a)

/--
AXIOM
-/
class has_left_unit [has_one α] [has_mul α]
    := (eq : Π a : α, 1 * a = a)

/--
-/
class has_add_le_add [has_le α] [has_add α]
    := (le : Π {a b c d : α}, a ≤ b → c ≤ d → a + c ≤ b + d)

/--
-/
class has_add_lt_add [has_lt α] [has_add α]
    := (lt : Π {a b c d : α}, a < b → c < d → a + c < b + d)

/--
-- try to remove and use has_lt_add_of_le_of_pos instead
-/
class has_le_add_of_nonneg_of_le [has_le α] [has_zero α] [has_add α]
    := (le : Π {a b c : α}, 0 ≤ a → b ≤ c → b ≤ a + c)

/--
-/
class has_lt_add_of_le_of_pos [has_le α] [has_lt α] [has_zero α] [has_add α]
    := (lt : Π {a b c : α}, 0 < a → b ≤ c → b < a + c)

/--
-- provable from has_add_le_add ...
-/
class has_add_nonneg [has_le α] [has_zero α] [has_add α]
    := (le : Π {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b)

/--
-/
class has_zero_mul_is_zero [has_zero α] [has_mul α]
    := (eq : Π a : α, 0 * a = 0)

/--
AXIOM
-/
class has_mul_zero_is_zero [has_zero α] [has_mul α]
    := (eq : Π a : α, a * 0 = 0)

/--
-/
class has_lift_zero_same [has_lift_t α β] [has_zero α] [has_zero β]
    := (eq : ↑(0 : α) = (0 : β))

/--
-/
class has_lift_one_same [has_lift_t α β] [has_one α] [has_one β]
    := (eq : ↑(1 : α) = (1 : β))

/--
provable from DD axioms
-/
class has_zero_right_add_cancel [has_zero α] [has_add α]
    := (eq : Π a : α, a + 0 = a)

/--
provable from has_double_sub_cancel
-/
class has_zero_left_add_cancel [has_zero α] [has_add α]
    := (eq : Π a : α, 0 + a = a)

/--
AXIOM
-/
class has_sub_self_is_zero [has_zero α] [has_sub α]
    := (eq : Π a : α, a - a = 0)

/--
AXIOM
-/
class has_mul_assoc [has_mul α]
    := (eq : Π a b c : α, (a * b) * c = a * (b * c))

/--
-/
class has_add_sub_assoc [has_add α] [has_sub α]
    := (eq : Π a b c : α, (a + b) - c = a + (b - c))

/--
-/
class has_le_sub_add_le [has_le α] [has_sub α] [has_add α]
    := (le : Π {a b c : α}, a ≤ c - b → a + b ≤ c)

/--
-/
class has_le_pos_mul_preserves_right [has_lt α] [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b c : α}, 0 < c → a ≤ b → a * c ≤ b * c)

/--
-/
class has_le_pos_mul_preserves_left [has_lt α] [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b c : α}, 0 < c → a ≤ b → c * a ≤ c * b)

/--
-/
class has_lt_pos_mul_preserves_right [has_lt α] [has_zero α] [has_mul α]
    := (lt : Π {a b c : α}, 0 < c → a < b → a * c < b * c)

/--
-/
class has_le_nonneg_mul_preserves_left [has_lt α] [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b c : α}, 0 ≤ c → a ≤ b → c * a ≤ c * b)

/--
-/
class has_le_nonneg_mul_preserves_right [has_lt α] [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b c : α}, 0 ≤ c → a ≤ b → a * c ≤ b * c)

/--
-/
class has_lift_le_comm [has_lift_t α β] [has_le α] [has_le β]
    := (le : Π {x y : α}, x ≤ y → ↑x ≤ (↑y : β))

/--
-/
class has_lift_lt_comm [has_lift_t α β] [has_lt α] [has_lt β]
    := (lt : Π {x y : α}, x < y → ↑x < (↑y : β))

/--
-/
class has_lift_ne_comm [has_lift_t α β]
    := (ne : Π {x y : α}, x ≠ y → ↑x ≠ (↑y : β))

/--
-/
class has_sub_add_sub_cancel [has_sub α] [has_add α]
    := (eq : Π a b c : α, a - b + (b - c) = a - c)

/--
-/
class has_double_sub_cancel [has_sub α]
    := (eq : Π a b : α, a - (a - b) = b)

/--
AXIOM
-/
class has_inv_mul_right_cancel_self [has_zero α] [has_one α] [has_inv α] [has_mul α]
    := (eq : Π a : α, a ≠ 0 → a * a⁻¹ = 1)

/--
-/
class has_inv_mul_left_cancel_self [has_zero α] [has_one α] [has_inv α] [has_mul α]
    := (eq : Π a : α, a ≠ 0 → a⁻¹ * a = 1)

/--
-/
class has_add_sub_exchange [has_add α] [has_sub α]
    := (eq : Π a b c d : α, (a - b) + (c - d) = (c - b) + (a - d))

/--
DEFINITION ("axiom")
-/
class has_zero_sub_is_neg [has_zero α] [has_neg α] [has_sub α]
    := (eq : Π a : α, 0 - a = -a)

/--
-/
class has_inv_right_mul_lt_pos [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, 0 < b → a < c * b → a * b⁻¹ < c)

/--
-/
class has_right_mul_inv_lt_pos [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, 0 < b → c < b⁻¹ * a → b * c < a)

/--
-/
class has_left_mul_inv_lt_pos [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, 0 < b → c < a * b⁻¹ → c * b < a)

/--
-/
class has_left_mul_inv_lt_neg [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, b < 0 → a * b⁻¹ < c → b * c < a)

/--
-/
class has_sub_ne_zero_of_ne [has_zero α] [has_sub α]
    := (ne : Π {a b : α}, a ≠ b → a - b ≠ 0)

/--
-/
class has_lt_sub_neg [has_lt α] [has_zero α] [has_sub α]
    := (lt : Π {a b : α}, a < b → a - b < 0)

/--
-/
class has_zero_lt_one [has_lt α] [has_zero α] [has_one α]
    := (lt : 0 < (1 : α))

/--
-/
class has_pos_mul_neg_is_neg [has_lt α] [has_zero α] [has_mul α]
    := (lt : Π {a b : α}, 0 < a → b < 0 → a * b < 0)

/--
-/
class has_nonneg_mul_nonneg_is_nonneg [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

/--
-/
class has_squared_le_monotonic [has_le α] [has_zero α] [has_mul α]
    := (le : Π {a b : α}, 0 ≤ a → a ≤ b → a * a ≤ b * b)

/--
-/
class has_sub_pos [has_lt α] [has_zero α] [has_sub α]
    := (lt : Π {a b : α}, a < b → 0 < b - a)

/--
-/
class has_sub_sub [has_add α] [has_sub α]
    := (eq : Π a b c : α, a - (b - c) = (a - b) + c)

/--
use reverse of has_lt_sub_neg?
-/
class has_add_left_lt [has_lt α] [has_add α]
    := (lt : Π a b c : α, a < b → c + a < c + b)

/--
-/
class has_left_inv_pos_lt [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, 0 < c → a < b → c⁻¹ * a < c⁻¹ * b)

/--
-/
class has_right_inv_pos_lt [has_lt α] [has_zero α] [has_mul α] [has_inv α]
    := (lt : Π {a b c : α}, 0 < c → a < b → a * c⁻¹ < b * c⁻¹)

/--
-/
class has_mul_pos [has_lt α] [has_zero α] [has_mul α]
    := (lt : Π {a b : α}, 0 < a → 0 < b → 0 < a * b)

/--
-/
class has_inv_pos [has_lt α] [has_zero α] [has_inv α]
    := (lt : Π {a : α}, 0 < a → 0 < a⁻¹)

/--
AXIOM
-/
class has_inv_reverses_le [has_le α] [has_inv α]
    := (le : Π {a b : α}, a ≤ b → b⁻¹ ≤ a⁻¹)

/--
AXIOM
-/
class has_inv_reverses_lt [has_lt α] [has_inv α]
    := (lt : Π {a b : α}, a < b → b⁻¹ < a⁻¹)

/--
-/
class has_inv_mul_reverse [has_inv α] [has_mul α]
    := (eq : Π a b : α, (a * b)⁻¹ = b⁻¹ * a⁻¹)

/--
-/
structure Half [has_lt α] [has_zero α] [has_add α]
    := (map          : α → α)
       (preserve_pos : Π {x}, 0 < x → 0 < map x)
       (doubled_inv  : Π (x), map x + map x = x)

/--
-/
structure LiftCeil [has_lift_t nat α] [has_lt α]
    := (map     : α → nat)
       (lift_lt : Π {a n}, map a < n → a < ↑n)

section lemmas --————————————————————————————————————————————————————————————————————————--
variables {α β}

/--
-/
def inv_sub_inv_lemma
    [has_zero α]
    [has_one α]
    [has_inv α]
    [has_mul α]
    [has_sub α]
    [has_right_unit α]
    [has_left_unit α]
    [has_inv_mul_right_cancel_self α]
    [has_mul_assoc α]
    [has_right_sub_distributivity α]
    {a b : α}
    (a_ne_0 : a ≠ 0)
    : a⁻¹ - b⁻¹ = (1 - b⁻¹ * a) * a⁻¹ :=
    begin
        rw has_right_sub_distributivity.eq,
        rw has_mul_assoc.eq,
        rw has_inv_mul_right_cancel_self.eq _ a_ne_0,
        rw has_left_unit.eq,
        rw has_right_unit.eq,
    end

/--
-/
def inv_sub_inv_lemma'
    [has_zero α]
    [has_one α]
    [has_inv α]
    [has_mul α]
    [has_sub α]
    [has_right_unit α]
    [has_left_unit α]
    [has_inv_mul_left_cancel_self α]
    [has_mul_assoc α]
    [has_left_sub_distributivity α]
    {a b : α}
    (a_ne_0 : a ≠ 0)
    : a⁻¹ - b⁻¹ = a⁻¹ * (1 - a * b⁻¹) :=
    begin
        rw has_left_sub_distributivity.eq,
        rw ← has_mul_assoc.eq,
        rw has_inv_mul_left_cancel_self.eq _ a_ne_0,
        rw has_left_unit.eq,
        rw has_right_unit.eq,
    end

/--
move to use location
-/
def mul_inv_add_one_lemma
    [has_lift_t nat α]
    [has_zero α]
    [has_one α]
    [has_sub α]
    [has_mul α]
    [has_inv α]
    [has_left_unit α]
    [has_inv_mul_right_cancel_self α]
    [has_right_sub_distributivity α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_sub_comm nat α]
    [has_lift_ne_comm nat α]
    (n : nat)
    : (↑n : α) * (↑n.succ)⁻¹ = 1 - (↑n.succ)⁻¹ :=
    begin
        rw ← has_left_unit.eq (↑n.succ : α)⁻¹,

        have succ_non_zero : ↑n.succ ≠ (0 : α),
            rw (_ : 0 = (↑0 : α)),
            refine has_lift_ne_comm.ne (nat.succ_ne_zero _),
            rw has_lift_zero_same.eq,

        rw ← has_inv_mul_right_cancel_self.eq _ succ_non_zero,
        rw ← has_right_sub_distributivity.eq,
        rw has_inv_mul_right_cancel_self.eq _ succ_non_zero,
        rw has_left_unit.eq,

        rw (_ : 1 = (↑1 : α)),

        rw ← has_lift_sub_comm.eq,
        rw nat.succ_sub_one,
        rw has_lift_one_same.eq,
    end

/--
-/
def two_mul_lemma
    [has_one α]
    [has_add α]
    [has_mul α]
    [has_right_add_distributivity α]
    [has_left_unit α]
    (a : α)
    : 2 * a = a + a :=
    begin
        refine (has_right_add_distributivity.eq _ _ _).trans _,
        rw has_left_unit.eq,
    end

/--
-/
def two_mul_lemma'
    [has_one α]
    [has_add α]
    [has_mul α]
    [has_left_add_distributivity α]
    [has_right_unit α]
    (a : α)
    : a * 2 = a + a :=
    begin
        refine (has_left_add_distributivity.eq _ _ _).trans _,
        rw has_right_unit.eq,
    end

/--
-/
def two_squares_is_four_lemma
    [has_one α]

    [has_add α] [has_mul α]

    [has_left_unit α]

    [has_left_add_distributivity α] [has_right_add_distributivity α]

    [has_mul_assoc α]

    (a : α)

    : 4 * (a * a) = (a + a) * (a + a) :=

    begin
        rw has_left_add_distributivity.eq,
        rw has_right_add_distributivity.eq,
        rw ← two_mul_lemma,
        rw ← two_mul_lemma,
        rw ← has_mul_assoc.eq,
        rw ← has_mul_assoc.eq,
        rw two_mul_lemma,
        rw has_mul_assoc.eq,

        refine rfl,
    end

/--
-/
def two_squares_is_four_lemma'
    [has_one α]

    [has_add α] [has_mul α]

    [has_right_unit α]

    [has_left_add_distributivity α] [has_right_add_distributivity α]

    [has_mul_assoc α]

    (a : α)

    : (a * a) * 4 = (a + a) * (a + a) :=

    begin
        rw has_right_add_distributivity.eq,
        rw has_left_add_distributivity.eq,
        rw ← two_mul_lemma',
        rw ← two_mul_lemma',
        rw has_mul_assoc.eq,
        rw has_mul_assoc.eq,
        rw two_mul_lemma',
        rw has_mul_assoc.eq,

        refine rfl,
    end

/--
-/
def nat_mul_commute_lemma
    [has_zero α]
    [has_one α]
    [has_add α]
    [has_mul α]

    [has_zero_mul_is_zero α]
    [has_mul_zero_is_zero α]

    [has_right_unit α]
    [has_left_unit α]

    [has_left_add_distributivity α]
    [has_right_add_distributivity α]

    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_add_comm nat α]

    (a : α) (n : nat)

    : a * ↑n = ↑n * a :=

    begin
        induction n with n hn,
            rw has_lift_zero_same.eq,
            rw has_zero_mul_is_zero.eq,
            rw has_mul_zero_is_zero.eq,
            rw nat.succ_eq_add_one,
            rw has_lift_add_comm.eq,
            rw has_left_add_distributivity.eq,
            rw has_right_add_distributivity.eq,
            rw hn,
            rw has_lift_one_same.eq,
            rw has_left_unit.eq,
            rw has_right_unit.eq,
    end

section lifted_lemmas --—————————————————————————————————————————————————————————————————--
variables (α β)

/--
-/
def zero_is_lifted_zero_lemma
    [has_zero α] [has_zero β] [has_lift_t α β] [has_lift_zero_same α β]
    : (0 : β) = ↑(0 : α)
    := by rw has_lift_zero_same.eq

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_one α] [has_one β] [has_lift_t α β] [has_lift_one_same α β]

/--
-/
def one_is_lifted_one_lemma
    : (1 : β) = ↑(1 : α)
    := by rw has_lift_one_same.eq

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_add α] [has_add β] [has_lift_add_comm α β]

/--
-/
def two_is_lifted_two_lemma : (2 : β) = ↑(2 : α) :=
    begin
        rw (_ : (2 : β) = ↑(1 : α) + ↑(1 : α)),
        rw ← has_lift_add_comm.eq,
        refine rfl,
        rw has_lift_one_same.eq,
        refine rfl,
    end

/--
-/
def three_is_lifted_three_lemma : (3 : β) = ↑(3 : α) :=
    begin
        rw (_ : (3 : β) = ↑(1 : α) + ↑(1 : α) + ↑(1 : α)),
        rw [← has_lift_add_comm.eq, ← has_lift_add_comm.eq],
        refine rfl,
        rw has_lift_one_same.eq,
        refine rfl,
    end

/--
-/
def four_is_lifted_four_lemma : (4 : β) = ↑(4 : α) :=
    begin
        rw (_ : (4 : β) = ↑(1 : α) + ↑(1 : α) + (↑(1 : α) + ↑(1 : α))),
        rw [← has_lift_add_comm.eq, ← has_lift_add_comm.eq],
        refine rfl,
        rw has_lift_one_same.eq,
        refine rfl,
    end

end lifted_lemmas --—————————————————————————————————————————————————————————————————————--
end lemmas --————————————————————————————————————————————————————————————————————————————--
end algebra --———————————————————————————————————————————————————————————————————————————--

namespace nat --—————————————————————————————————————————————————————————————————————————--

/--
-/
def of_le_succ {n m : nat} (n_le_m_succ : n ≤ m.succ) : n ≤ m ∨ n = m.succ
    := (lt_or_eq_of_le n_le_m_succ).imp le_of_lt_succ id

/--
-/
def sub_sub_sub_cancel_right {a b c} (c_le_b : c ≤ b) : a - c - (b - c) = a - b
    := by rw [nat.sub_sub, ← nat.add_sub_assoc c_le_b, nat.add_sub_cancel_left]

/--
-/
def le_sub_right_of_add_le {m n k} : m + k ≤ n → m ≤ n - k :=
    begin
        intros h,
        rw ← nat.add_sub_cancel m k,
        refine nat.sub_le_sub_right h _,
    end

/--
-/
def le_sub_left_of_add_le {k m n} (h : k + m ≤ n) : m ≤ n - k
    := le_sub_right_of_add_le (by { rw ← nat.add_comm, refine h })

/--
-/
def le_add_of_sub_le_right {k m n} : n - k ≤ m → n ≤ m + k :=
    begin
        intros h,
        rw ← nat.add_sub_cancel m k at h,
        refine (nat.sub_le_sub_right_iff _ _ _ (nat.le_add_left _ _)).mp h,
    end

/--
-/
def add_lt_add_of_le_of_lt {a b c d} (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d
    := lt_of_le_of_lt (nat.add_le_add_right h₁ c) (nat.add_lt_add_left h₂ b)

/--
-/
def lt_add_of_le_of_pos {a b c} (b_le_c : b ≤ c) (zero_lt_a : 0 < a) : b < c + a
    := nat.add_zero b ▸ nat.add_lt_add_of_le_of_lt b_le_c zero_lt_a

/--
-/
def neg_right_swap {a b c} (c_le_b : c ≤ b) :  a - (b - c) = (a + c) - b :=
    begin
        rw ← nat.add_sub_cancel a _,
        rw nat.sub_sub_sub_cancel_right c_le_b,
        rw nat.add_sub_assoc (le_refl _),
        rw nat.sub_self,
        rw nat.add_zero,
    end

/--
-/
def sub_mono_left_strict {x y z : nat} (z_le_x : z ≤ x) (x_lt_y : x < y)
    : x - z < y - z :=
    begin
        refine @nat.lt_of_add_lt_add_left z _ _ _,
        rw add_sub_of_le (le_trans z_le_x (le_of_lt x_lt_y)),
        rw add_sub_of_le z_le_x,
        refine x_lt_y,
end

/--
-/
def mul_two (n) : n * 2 = n + n :=
    begin
        refine (nat.left_distrib _ _ _).trans _,
        rw nat.mul_one,
    end

/--
-/
def pow_two_ge_one (n : nat) : 1 ≤ 2 ^ n :=
    begin
        induction n with n hn,
            refine le_refl _,
            refine le_trans hn (le_add_left _ _),
    end

/--
-/
def pow_two_monotonic (n : nat) : 2 ^ n < 2 ^ n.succ
    := lt_add_of_le_of_pos (nat.le_add_left _ _) (pow_two_ge_one _)

/--
-/
def smallest_positive_even (n : nat)
    : 2 ≤ 2 * n.succ :=
    begin
        induction n with n hn,
            rw nat.mul_one,
            refine le_trans hn (nat.le.intro rfl),
    end

/--
-/
def successive_difference (u : nat → nat) (n : nat)
    := u n.succ - u n

/--
-/
def power [has_one α] [has_mul α] (a : α) : nat → α
| (nat.zero  ) := 1
| (nat.succ n) := power n * a

namespace power --———————————————————————————————————————————————————————————————————————--
variables [has_one α] [has_mul α]

/--
-/
def mul_commute
    [has_one β] [has_mul β]
    (map     : α → β)
    (map_one : map 1 = 1)
    (map_mul : Π x y, map (x * y) = map x * map y)
    (a : α) (n)
    : map (power a n) = power (map a) n :=
    begin
        induction n with n hn,
            rw [power, power],
            rw map_one,
            rw [power, power],
            rw map_mul,
            rw hn,
    end

end power --—————————————————————————————————————————————————————————————————————————————--

namespace lift --————————————————————————————————————————————————————————————————————————--
variables (α)

/--
-/
def succ_pos
    [has_lt α]
    [has_zero α]
    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_lt_comm nat α]
    (n : nat)
    : 0 < (↑n.succ : α) :=
    begin
        rw zero_is_lifted_zero_lemma ℕ α,
        refine has_lift_lt_comm.lt (nat.succ_pos _),
    end

/--
-/
def succ_nonzero
    [preorder α]
    [has_zero α]
    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_lt_comm nat α]
    (n : nat)
    : (↑n.succ : α) ≠ 0
    := (ne_of_gt (nat.lift.succ_pos α _))

/--
-/
def zero_lt_one
    [has_lt α]
    [has_zero α]
    [has_one α]
    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_lt_comm nat α]
    : (0 : α) < 1 :=
    begin
        rw one_is_lifted_one_lemma nat α,
        refine nat.lift.succ_pos α _,
    end

/--
-/
instance zero_lt_one_instance
    [has_lt α]
    [has_zero α]
    [has_one α]
    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_lt_comm nat α]
    : has_zero_lt_one α
    := ⟨zero_lt_one α⟩

end lift --——————————————————————————————————————————————————————————————————————————————--
end nat --———————————————————————————————————————————————————————————————————————————————--

section sequences --—————————————————————————————————————————————————————————————————————--

/--
-/
def strictly_increasing
    [has_lt α]
    (seq : nat → α)
    := Π n, seq n < seq n.succ

/--
-/
def increasing
    [has_le α]
    (seq : nat → α)
    := Π n, seq n ≤ seq n.succ

/--
-/
def strictly_increasing.as_increasing
    [preorder α]
    (seq : nat → α)
    : strictly_increasing seq → increasing seq :=
    begin
        intros sinc _,
        refine le_of_lt (sinc _),
    end

/--
-/
def increasing_strong
    [has_le α]
    (seq : nat → α)
    := Π i j, i ≤ j → seq i ≤ seq j

/--
-/
def increasing.as_increasing_strong
    [preorder α]
    (seq : nat → α)
    : increasing seq → increasing_strong seq :=
    begin
        intros inc i j i_le_j,
        induction j with j hj,
            cases i_le_j,
                refine le_refl _,
            cases nat.of_le_succ i_le_j,
                refine le_trans (hj h) (inc _),
                rw h,
    end

/--
-/
def strictly_increasing.as_increasing_strong
    [preorder α]
    (seq : nat → α)
    : strictly_increasing seq → increasing_strong seq
    := λ s, increasing.as_increasing_strong _ (strictly_increasing.as_increasing _ s)

/--
-/
def non_increasing
    [has_le α]
    (seq : nat → α)
    := Π n, seq (nat.succ n) ≤ seq n

/--
-/
def non_increasing_strong
    [has_le α]
    (seq : nat → α) (k)
    := Π n, seq (n + k) ≤ seq n

/--
-/
def non_increasing.as_non_increasing_strong
    [preorder α]
    (seq : nat → α)
    : non_increasing seq → Π k, non_increasing_strong seq k :=
    begin
        intros noninc k _,
        induction k with k hk,
            refine le_refl _,
            refine le_trans (noninc _) hk,
    end

/--
-/
def strictly_increasing.ge_index
    (seq) (sinc : strictly_increasing seq)
    (k)
    : k ≤ seq k :=
    begin
        induction k with _ hk,
            refine nat.zero_le _,
            rw nat.succ_eq_add_one,
            refine le_trans (nat.add_le_add hk (le_refl _)) (sinc _),
    end

/--
-/
def nonneg_compose_preserve
    [has_zero α] [has_le α]
    (seq : nat → α) (φ : nat → nat)
    : 0 ≤ seq → 0 ≤ seq ∘ φ
    := λ p _, p (φ _)

/--
-/
def translate
    (seq : nat → α)
    (k)
    (n)
    := seq (k + n)

/--
-/
def translate.preserve_nonneg
    [has_zero α] [has_le α]
    (seq : nat → α)
    : 0 ≤ seq → 0 ≤ translate seq
    := λ p _ _, p _

/--
-/
def translate.monotonicity
    [has_le α]
    {a b : nat → α}
    : a ≤ b → translate a ≤ translate b
    := λ p _ _, p _

/--
-/
def translate.combine
    (seq : nat → α)
    (i j)
    : translate (translate seq i) j = translate seq (i + j)
    := funext (λ _, by rw [translate, translate, translate, nat.add_assoc])

/--
-/
def translate.compose_commute
    (seq : nat → α)
    (f : α → β)
    (n k)
    : f (translate seq n k) = translate (f ∘ seq) n k
    := by rw [translate, translate]

/--
-/
def translate.compose_commute.funext
    (seq : nat → α)
    (f : α → β)
    (n)
    : f ∘ (translate seq n) = translate (f ∘ seq) n
    := funext (translate.compose_commute seq f n)

end sequences --—————————————————————————————————————————————————————————————————————————--

section series --————————————————————————————————————————————————————————————————————————--
variables [has_zero α] [has_add α]

/--
-/
def partial_sum (seq : nat → α) : nat → α
| (nat.zero  ) := 0
| (nat.succ n) := seq n + partial_sum n

/--
-/
def partial_sum.preserve_nonneg
    [preorder α] [has_add_nonneg α]

    (seq : nat → α)

    : 0 ≤ seq → 0 ≤ partial_sum seq :=

    begin
        intros nonneg k,
        induction k with k hk,
            refine le_refl _,
            refine has_add_nonneg.le (nonneg _) hk,
    end

/--
-/
def partial_sum.left_mul_commute
    [has_mul α] [has_mul_zero_is_zero α] [has_left_add_distributivity α]
    (seq : nat → α)
    (C)
    : partial_sum (λ k, C * seq k) = λ n, C * partial_sum seq n :=
    begin
        refine funext _,
        intros n,
        induction n with n hn,
            rw partial_sum,
            rw partial_sum,
            rw has_mul_zero_is_zero.eq,
            rw partial_sum,
            rw partial_sum,
            rw hn,
            rw has_left_add_distributivity.eq,
    end

/--
-/
def partial_sum.right_mul_commute
    [has_mul α] [has_zero_mul_is_zero α] [has_right_add_distributivity α]
    (seq : nat → α)
    (C)
    : partial_sum (λ k, seq k * C) = λ n, partial_sum seq n * C :=
    begin
        refine funext _,
        intros n,
        induction n with n hn,
            rw partial_sum,
            rw partial_sum,
            rw has_zero_mul_is_zero.eq,
            rw partial_sum,
            rw partial_sum,
            rw hn,
            rw has_right_add_distributivity.eq,
    end

/--
-/
def partial_sum.from_mul
    [has_one α]
    [has_mul α]

    [has_zero_mul_is_zero α]
    [has_left_unit α]
    [has_right_add_distributivity α]

    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_add_comm nat α]

    (a : α)
    (n : nat)

    : ↑n * a = partial_sum ↓a n :=

    begin
        induction n with n hn,
            rw partial_sum,
            rw has_lift_zero_same.eq,
            rw has_zero_mul_is_zero.eq,
            rw partial_sum,
            rw nat.succ_eq_add_one,
            rw nat.add_comm,
            rw has_lift_add_comm.eq,
            rw has_right_add_distributivity.eq,
            rw has_lift_one_same.eq,
            rw has_left_unit.eq,
            rw hn,
            rw const,
    end

/--
-/
def partial_sum.from_mul'
    [has_one α]
    [has_mul α]

    [has_mul_zero_is_zero α]
    [has_right_unit α]
    [has_left_add_distributivity α]

    [has_lift_t nat α]
    [has_lift_zero_same nat α]
    [has_lift_one_same nat α]
    [has_lift_add_comm nat α]

    (a : α)
    (n : nat)

    : a * ↑n = partial_sum ↓a n :=

    begin
        induction n with n hn,
            rw partial_sum,
            rw has_lift_zero_same.eq,
            rw has_mul_zero_is_zero.eq,
            rw partial_sum,
            rw nat.succ_eq_add_one,
            rw nat.add_comm,
            rw has_lift_add_comm.eq,
            rw has_left_add_distributivity.eq,
            rw has_lift_one_same.eq,
            rw has_right_unit.eq,
            rw hn,
            rw const,
    end

/--
-/
def partial_sum.monotonicity
    [preorder α] [has_add_le_add α]
    {a b : nat → α}
    : a ≤ b → partial_sum a ≤ partial_sum b :=
    begin
        intros a_le_b n,
        induction n with _ hn,
            refine le_refl _,
            refine has_add_le_add.le (a_le_b _) hn,
    end

/--
-/
def partial_sum.index_monotonicity
    [preorder α] [has_le_add_of_nonneg_of_le α]

    (seq : nat → α) (nonneg : 0 ≤ seq)

    {m n}

    : m ≤ n → partial_sum seq m ≤ partial_sum seq n :=

    begin
        intros m_le_n,
        induction n with n hn,
            cases m_le_n,
                refine le_refl _,
            cases nat.of_le_succ m_le_n,
                refine has_le_add_of_nonneg_of_le.le (nonneg _) (hn h),
                rw ← h,
    end

/--
-/
def partial_sum.double_monotonicity
    [preorder α] [has_le_add_of_nonneg_of_le α] [has_add_le_add α]

    (a : nat → α) (na)
    (b : nat → α) (nb)

    : 0 ≤ a → a ≤ b → na ≤ nb → partial_sum a na ≤ partial_sum b nb :=

    begin
        intros zero_le_a a_le_b na_le_nb,
        induction nb with _ hnb,
            cases na_le_nb,
                refine le_refl _,
            cases nat.of_le_succ na_le_nb,
                refine has_le_add_of_nonneg_of_le.le
                    (le_trans (zero_le_a _) (a_le_b _)) (hnb h),
                rw h,
                refine has_add_le_add.le
                    (a_le_b _) (partial_sum.monotonicity a_le_b _),
    end

/--
-/
def partial_sum.sub_as_translate
    [has_sub α] [has_sub_self_is_zero α] [has_add_sub_assoc α]

    (seq : nat → α)

    {m n} (m_le_n : m ≤ n)

    : partial_sum seq n - partial_sum seq m = partial_sum (translate seq m) (n - m) :=

    begin
        induction n with n hn,
            cases m_le_n,
                refine has_sub_self_is_zero.eq _,
            cases m_le_n with _ m_le_n,
                rw has_sub_self_is_zero.eq,
                rw nat.sub_self,
                rw partial_sum,
                rw partial_sum,
                rw has_add_sub_assoc.eq,
                rw hn m_le_n,
                rw nat.succ_sub m_le_n,
                rw partial_sum,
                rw translate,
                rw nat.add_sub_of_le m_le_n,
    end

/--
-/
def partial_sum.lower_differences.bottom
    [has_sub α]
    [has_add_sub_assoc α]
    [has_sub_self_is_zero α]

    [preorder α]
    [has_le_add_of_nonneg_of_le α]

    (seq : nat → α) (nonneg : 0 ≤ seq)

    {m n} (m_le_n : m ≤ n)

    : 0 ≤ partial_sum seq n - partial_sum seq m :=

    begin
        induction n with n hn,
            cases m_le_n,
                rw has_sub_self_is_zero.eq,
            cases nat.of_le_succ m_le_n,
                rw partial_sum,
                rw has_add_sub_assoc.eq,
                refine has_le_add_of_nonneg_of_le.le (nonneg _) (hn h),
                rw ← h,
                rw has_sub_self_is_zero.eq,
    end

/--
-/
def partial_sum.lower_differences
    [has_sub α]
    [has_sub_self_is_zero α]
    [has_add_sub_assoc α]

    [preorder α]
    [has_add_le_add α]
    [has_le_add_of_nonneg_of_le α]

    (seq : nat → α) (nonneg : 0 ≤ seq)

    {k m n} (k_le_m : k ≤ m) (m_le_n : m ≤ n)

    : partial_sum seq n - partial_sum seq m ≤ partial_sum seq n - partial_sum seq k :=

    begin
        induction n with n hn,
            cases m_le_n,
                cases k_le_m,
                    refine le_refl _,
            cases nat.of_le_succ m_le_n,
                rw partial_sum,
                rw has_add_sub_assoc.eq,
                rw has_add_sub_assoc.eq,
                refine has_add_le_add.le (le_refl _) (hn h),
                rw ← h,
                rw has_sub_self_is_zero.eq,
                refine partial_sum.lower_differences.bottom _ nonneg k_le_m,
    end

--———————————————————————————————————————————————————————————————————————————————————————--
variables [has_sub α]

/--
-/
def shape_sum (seq : nat → α) (φ : nat → nat) (n : nat)
    := partial_sum seq (φ n.succ) - partial_sum seq (φ n)

/--
-/
def shape_sum.unfold
    [has_sub_self_is_zero α]
    [has_add_sub_assoc α]
    [has_sub_add_sub_cancel α]

    (seq : nat → α)

    (φ) (sinc_φ : strictly_increasing φ)

    {m n} (m_le_n : m ≤ n)

    : partial_sum (translate (shape_sum seq φ) m) (n - m)
    = partial_sum (translate seq (φ m)) (φ n - φ m) :=

    begin
        let strong_inc := strictly_increasing.as_increasing_strong _ sinc_φ,
        induction n with n hn,
            cases m_le_n,
                rw [nat.sub_self, nat.sub_self, partial_sum, partial_sum],
            cases nat.of_le_succ m_le_n,
                rw nat.succ_sub h,
                rw partial_sum,
                rw hn h,
                rw translate,
                rw nat.add_sub_of_le h,
                rw shape_sum,
                rw ← partial_sum.sub_as_translate seq (strong_inc _ _ h),
                rw ← partial_sum.sub_as_translate seq (strong_inc _ _ m_le_n),
                rw has_sub_add_sub_cancel.eq,
                rw h,
                rw [nat.sub_self, nat.sub_self, partial_sum, partial_sum],
    end

end series --————————————————————————————————————————————————————————————————————————————--

section absolute_value --————————————————————————————————————————————————————————————————--
variables [has_zero α] [has_add α]

/--
-/
def triangle_inequality
    [has_zero β] [has_add β] [preorder β] [has_add_le_add β]

    (abs          : α → β)
    (abs_zero     : abs 0 = 0)
    (abs_triangle : Π x y, abs (x + y) ≤ abs x + abs y)

    (seq) (n)

    : abs (partial_sum seq n) ≤ partial_sum (abs ∘ seq) n :=

    begin
        induction n with _ hn,
            rw [partial_sum, partial_sum],
            rw abs_zero,
            refine le_trans (abs_triangle _ _) (has_add_le_add.le (le_refl _) hn),
    end

/--
-/
def triangle_equality
    [preorder α] [has_add_nonneg α]

    (abs           : α → α)
    (nonneg_to_abs : Π z, 0 ≤ z → abs z = z)

    (seq nonneg) (n)

    : abs (partial_sum seq n) = partial_sum seq n

    := nonneg_to_abs _ (partial_sum.preserve_nonneg _ nonneg _)

end absolute_value --————————————————————————————————————————————————————————————————————--
