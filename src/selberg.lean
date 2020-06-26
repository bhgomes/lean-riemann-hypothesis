-- @file:   selberg.lean
-- @author: Brandon H. Gomes
-- @affil:  Rutgers University
-- @source: arXiv:1308.3067v2 [math.NT] 13 Feb 2015

/-!
# Selberg Class

...
-/

section basic --—————————————————————————————————————————————————————————————————————————--

/--
`Power X` (`𝒫 X`) The powerset of a type.
-/
def Power (X : Sort*)
    := X → Sort*
notation `𝒫` X := Power X

/--
`const b` (`↓b`) The constant function at a point.
-/
def const {X Y : Type*}
    := λ b : Y, (λ x : X, b)
notation `↓`:max y:max := const y

/--
-/
instance pointwise_lt {X Y : Type*} [has_lt Y] : has_lt (X → Y)
    := ⟨λ f g, (Π x, f x < g x)⟩

/--
-/
instance lt_has_le {Y : Type*} [has_lt Y] : has_le Y
    := ⟨λ p q, p < q ∨ p = q⟩

/--
-/
def is_same {X : Type*} (I : X → X)
    := λ x, I x = x
notation x `∈` I := is_same I x

/--
-/
structure membership {X : Type*} (I : X → X)
    := (elem      : X)
       (is_member : elem ∈ I)

end basic --—————————————————————————————————————————————————————————————————————————————--

namespace membership --——————————————————————————————————————————————————————————————————--
variables {X : Type*} (I : X → X)

/- --- -/

end membership --————————————————————————————————————————————————————————————————————————--

section analysis --——————————————————————————————————————————————————————————————————————--

/--
-/
def supp {X Y : Type*} [has_zero Y] (f : X → Y)
    := λ x, f x ≠ 0

end analysis --——————————————————————————————————————————————————————————————————————————--

section difference_domain --—————————————————————————————————————————————————————————————--
variables (C : Type*) [has_zero C] [has_sub C] [has_mul C]

/--
-/
structure DifferenceDomain
    := (sub_cancel       : Π z : C, z - z = 0)
       (sub_right_id     : Π z : C, z - 0 = z)
       (mul_right_absorb : Π z : C, z * 0 = 0)

end difference_domain --—————————————————————————————————————————————————————————————————--

section subdomain --—————————————————————————————————————————————————————————————————————--
variables (C : Type*) [has_zero C] [has_sub C] [has_mul C]

/--
-/
structure SubDomain
    := (proj         : C → C)
       (idempotent   : Π z, proj (proj z) = proj z)
       (respects_sub : Π x y, proj (x - y) = proj x - proj y)
       (respects_mul : Π x y, proj (x * y) = proj x * proj y)

--———————————————————————————————————————————————————————————————————————————————————————--
variables {C} (S : SubDomain C)

/--
-/
def SubDomain.membership
    := membership S.proj

/--
-/
def SubDomain.member (z) : S.membership
    := ⟨S.proj z, S.idempotent z⟩

end subdomain --—————————————————————————————————————————————————————————————————————————--

section complex --———————————————————————————————————————————————————————————————————————--
variables (C : Type*) [has_zero C] [has_one C] [has_sub C] [has_mul C]

/--
-/
structure Complex extends DifferenceDomain C
    := (Real            : SubDomain C)
       (Int             : SubDomain C)
       (abs             : C → membership Real.proj)
       (int_is_real     : Π {z}, z ∈ Int.proj → z ∈ Real.proj)
       (zero_is_int     : (0 : C) ∈ Int.proj)
       (one_is_int      : (1 : C) ∈ Int.proj)
       (real_lt         : membership Real.proj → membership Real.proj → Prop)
       (zero_lt_one     : real_lt ⟨_, int_is_real zero_is_int⟩ ⟨_, int_is_real one_is_int⟩)

--———————————————————————————————————————————————————————————————————————————————————————--
variables {C} (ℂ : Complex C)

/--
-/
def Complex.int
    := ℂ.Int.proj

/--
-/
def Complex.Z
    := ℂ.Int.member

/--
-/
def Complex.real
    := ℂ.Real.proj

/--
-/
def Complex.Re
    := ℂ.Real.member

/--
-/
def Complex.Imag : SubDomain C
    := { proj := λ z, z - ℂ.real z,
         idempotent := sorry,
         respects_sub := sorry,
         respects_mul := sorry, }

/--
-/
def Complex.imag
    := ℂ.Imag.proj

/--
-/
def Complex.Im
    := ℂ.Imag.member

/--
-/
instance Complex.real_has_lt : has_lt ℂ.Real.membership
    := ⟨ℂ.real_lt⟩

/--
-/
def Complex.int_lt (m n : ℂ.Int.membership)
    := ℂ.real_lt ⟨m.elem, ℂ.int_is_real m.is_member⟩
                 ⟨n.elem, ℂ.int_is_real n.is_member⟩

/--
-/
instance Complex.int_has_lt : has_lt ℂ.Int.membership
    := ⟨ℂ.int_lt⟩

/--
-/
def Complex.zero_int : ℂ.Int.membership
    := ⟨0, ℂ.zero_is_int⟩

/--
-/
instance Complex.int_has_zero : has_zero ℂ.Int.membership
    := ⟨ℂ.zero_int⟩

/--
-/
def Complex.zero_real : ℂ.Real.membership
    := ⟨0, ℂ.int_is_real ℂ.zero_is_int⟩

/--
-/
instance Complex.real_has_zero : has_zero ℂ.Real.membership
    := ⟨ℂ.zero_real⟩

/--
-/
def Complex.one_int : ℂ.Int.membership
    := ⟨1, ℂ.one_is_int⟩

/--
-/
instance Complex.int_has_one : has_one ℂ.Int.membership
    := ⟨ℂ.one_int⟩

/--
-/
def Complex.one_real : membership ℂ.real
    := ⟨1, ℂ.int_is_real ℂ.one_is_int⟩

/--
-/
instance Complex.real_has_one : has_one ℂ.Real.membership
    := ⟨ℂ.one_real⟩

/--
-/
structure Complex.ℝpos extends membership ℂ.real
    := (is_pos : ℂ.real_lt ℂ.zero_real to_membership)

/--
-/
def Complex.one_real_pos : ℂ.ℝpos
    := ⟨ℂ.one_real, ℂ.zero_lt_one⟩

/--
-/
instance Complex.real_pos_has_one : has_one ℂ.ℝpos
    := ⟨ℂ.one_real_pos⟩

/--
-/
structure Complex.ℤpos extends membership ℂ.int
    := (is_pos : ℂ.int_lt ℂ.zero_int to_membership)

/--
-/
def Complex.one_int_pos : ℂ.ℤpos
    := ⟨ℂ.one_int, ℂ.zero_lt_one⟩

/--
-/
instance Complex.int_pos_has_one : has_one ℂ.ℤpos
    := ⟨ℂ.one_int_pos⟩

end complex --———————————————————————————————————————————————————————————————————————————--

section LDatum --————————————————————————————————————————————————————————————————————————--

variables {C : Type*} [has_zero C] [has_one C] [has_sub C] [has_mul C]
          (ℂ : Complex C)

local notation `ℝ` := ℂ.Real.membership
local notation `ℝ₀` := ℂ.ℝpos
local notation `ℤ` := ℂ.Int.membership
local notation `ℤ₀` := ℂ.ℤpos
local notation `ℜ` := ℂ.Re
local notation `ℑ` := ℂ.Im

local notation `|` z `|` := ℂ.abs z

/--
A1:
- f(1) ∈ ℝ
- ∀k > 0, f(n) * log^k n <<_k 1
- ∀ε > 0, ∑_{n ≤ x}|f(n)|^2 <<_ε x^ε
-/
structure Axiom1 (f : ℤ₀ → C)
    := (bounded : (ℤ₀ → C) → (C → C) → Type*)
       (real_at_one : f 1 ∈ ℂ.real)
       (log_bound   : bounded f ↓1)
       (sum_bound   : empty)

/--
A2:
- x*K(x) extends to a Schwartz function on ℝ
- lim_{x→0^+}(x * K(x)) ∈ ℝ
-/
structure Axiom2 (K : ℝ₀ → C)
    := (extends_to_schwartz : (ℝ₀ → C) → 𝒫 C → Type*)
       (lim0 : (ℝ₀ → C) → C)
       (schwartz_extension : extends_to_schwartz (λ x, x.elem * K x) (λ x, x ∈ ℂ.real))
       (real_limit         : lim0 (λ x, x.elem * K x) ∈ ℂ.real)

/--
A3:
- supp(m) := { z ∈ ℂ | m (z) ≠ 0 } is discrete(?) and contained in a horizontal strip
    { z ∈ ℂ | |ℑ(z)| ≤ y} for some y ≥ 0
- ∑_{z ∈ supp(m), |ℜ(z)| ≤ T} |m(z)| << 1 + T^A for some A ≥ 0
- #{z ∈ supp(m) | m(z) ∉ ℤ} < ∞
-/
structure Axiom3 (m : C → ℝ)
    := (is_discrete : 𝒫 C → Type*) (has_bounded_count : 𝒫 C → Type*)
       (discrete_support       : is_discrete (supp m))
       -- (horizontal_support     : ∃ y ≥ 0, (Π z, supp m z → |(ℑ z).elem| ≤ y))
       (support_sum_bound      : empty)
       (finite_non_int_support : has_bounded_count (λ z, supp m z ∧ ¬((m z).elem ∈ ℂ.int)))

/--
A4:
- ∀ smooth g : ℝ → ℂ of compact support and Fourier Transform h(z) = ∫_ℝ g(x)e^{ixz}dx
    satisfying h(ℝ) ⊆ ℝ, we have the equality:
        ∑_{z∈supp(m)}m(z)h(z) = 2*ℜ( ∫_0^∞ K(x)(g(0) - g(x))dx - ∑_{n=1}^∞ f(n)g(log n) )
-/
structure Axiom4 (f : ℤ₀ → C) (K : ℝ₀ → C) (m : C → ℝ)
    := (is_smooth : (ℝ → C) → Type*)
       (is_compact : Π {X : Type*}, 𝒫 X → Type*)
       (fourier_transform : (ℝ → C) → (C → C))
       (special_equality : Type*)
       (fourier_equality : Π (g) {_ : is_smooth g} {_ : is_compact (supp g)}, special_equality)

/--
-/
structure LDatum
    := (f : ℤ₀ → C)
       (K : ℝ₀ → C)
       (m : C → ℝ)
       (A1 : Axiom1 ℂ f)
       (A2 : Axiom2 ℂ K)
       (A3 : Axiom3 ℂ m)
       (A4 : Axiom4 ℂ f K m)

/--
L-Function
- L_F(s) := ∑_{n=1}^∞ a_F(n) n^-s = exp(∑_{n=2}^∞ f(n) / log(n) * n ^ {1/2 - s}) for ℜ(s) > 1
-/
def LDatum.L (L : LDatum ℂ)
    (exp : C → C) (sum : (ℤ₀ → C) → C) (inv_log : ℤ₀ → C) (pow : ℤ₀ → C → C) (inv_two : C)
    (s : C) (σ1 : ℜ s > 1)
    := exp (sum (λ n, L.f n * inv_log n * pow n (inv_two - s))) -- sum starting from n = 2 ...?

/--
Degree of F
- d_F := 2 * lim_{x → 0^+} xK(x)
-/
def LDatum.degree (L : LDatum ℂ) (two : C) (lim0 : (ℝ₀ → C) → C)
    := two * lim0 (λ x, x.elem * L.K x)

/--
Analytic Conductor of F
- Q_F := e^(-2f(1))
-/
def LDatum.conductor (L : LDatum ℂ) (exp : C → C) (minus_two : C)
    := exp (minus_two * L.f 1)

/--
F is positive if
- there are at most finitely many z ∈ ℂ with m(z) < 0
-/
def LDatum.is_positive (L : LDatum ℂ) (finitely_many_negative : (C → ℝ) → Type*)
    := finitely_many_negative L.m

end LDatum --————————————————————————————————————————————————————————————————————————————--
