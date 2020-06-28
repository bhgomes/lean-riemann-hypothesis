/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    selberg.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
| @source:  arXiv:1308.3067v2 [math.NT] 13 Feb 2015                           |
\- ------------------------------------------------------------------------- -/

import .complex
import .reduction

/-!
# Selberg Class

...
-/

section analysis --——————————————————————————————————————————————————————————————————————--
/--
-/
def supp {X Y : Type*} [has_zero Y] (f : X → Y)
    := λ x, f x ≠ 0
end analysis --——————————————————————————————————————————————————————————————————————————--


--———————————————————————————————————————————————————————————————————————————————————————--
variables {ℂ : Type*} [has_one ℂ] [DifferenceDomain ℂ] (ℭ : Complex ℂ)

local notation `ℝ` := membership ℭ.real
local notation `ℤ` := membership ℭ.int
local notation `ℝ₀` := ℭ.ℝpos
local notation `ℤ₀` := ℭ.ℤpos
local notation `ℜ` := ℭ.Re
local notation `ℑ` := ℭ.Im

local notation `|` z `|` := ℭ.abs z

namespace LDatum --——————————————————————————————————————————————————————————————————————--

/--
A1:
- f(1) ∈ ℝ
- ∀k > 0, f(n) * log^k n <<_k 1
- ∀ε > 0, ∑_{n ≤ x}|f(n)|^2 <<_ε x^ε
-/
structure Axiom1 (f : ℤ₀ → ℂ)
    := (bounded     : (ℤ₀ → ℂ) → (ℂ → ℂ) → Type*)
       (real_at_one : f 1 ~ ℭ.real)
       (log_bound   : bounded f ↓1)
       (sum_bound   : empty)

/--
A2:
- x*K(x) extends to a Schwartz function on ℝ
- lim_{x→0^+}(x * K(x)) ∈ ℝ
-/
structure Axiom2 (K : ℝ₀ → ℂ)
    := (extends_to_schwartz : (ℝ₀ → ℂ) → 𝒫 ℂ → Type*)
       (lim0                : (ℝ₀ → ℂ) → ℂ)
       (schwartz_extension  : extends_to_schwartz (λ x, x.elem * K x) (λ x, x ~ ℭ.real))
       (real_limit          : lim0 (λ x, x.elem * K x) ~ ℭ.real)

/--
A3:
- supp(m) := { z ∈ ℂ | m (z) ≠ 0 } is discrete(?) and contained in a horizontal strip
    { z ∈ ℂ | |ℑ(z)| ≤ y} for some y ≥ 0
- ∑_{z ∈ supp(m), |ℜ(z)| ≤ T} |m(z)| << 1 + T^A for some A ≥ 0
- #{z ∈ supp(m) | m(z) ∉ ℤ} < ∞
-/
structure Axiom3 (m : ℂ → ℝ)
    := (is_discrete            : 𝒫 ℂ → Type*)
       (has_bounded_count      : 𝒫 ℂ → Type*)
       (discrete_support       : is_discrete (supp m))
       (horizontal_support     : ∃ y ≥ 0, (Π z, supp m z → |(ℑ z).elem| ≤ y))
       (support_sum_bound      : empty)
       (finite_non_int_support : has_bounded_count (λ z, supp m z ∧ ¬((m z).elem ~ ℭ.int)))

/--
A4:
- ∀ smooth g : ℝ → ℂ of compact support and Fourier Transform h(z) = ∫_ℝ g(x)e^{ixz}dx
    satisfying h(ℝ) ⊆ ℝ, we have the equality:
        ∑_{z∈supp(m)}m(z)h(z) = 2*ℜ( ∫_0^∞ K(x)(g(0) - g(x))dx - ∑_{n=1}^∞ f(n)g(log n) )
-/
structure Axiom4 (f : ℤ₀ → ℂ) (K : ℝ₀ → ℂ) (m : ℂ → ℝ)
    := (is_smooth         : (ℝ → ℂ) → Type*)
       (is_compact        : Π {X : Type*}, 𝒫 X → Type*)
       (fourier_transform : (ℝ → ℂ) → (ℂ → ℂ))
       (special_equality  : Type*)
       (fourier_equality  : Π (g) {_ : is_smooth g} {_ : is_compact (supp g)}, special_equality)

end LDatum --————————————————————————————————————————————————————————————————————————————--

/--
-/
structure LDatum
    := (f  : ℤ₀ → ℂ)
       (K  : ℝ₀ → ℂ)
       (m  : ℂ → ℝ)
       (a1 : LDatum.Axiom1 ℭ f)
       (a2 : LDatum.Axiom2 ℭ K)
       (a3 : LDatum.Axiom3 ℭ m)
       (a4 : LDatum.Axiom4 ℭ f K m)

namespace LDatum --——————————————————————————————————————————————————————————————————————--
variables (L : LDatum ℭ)

/--
L-Function
- L_F(s) := ∑_{n=1}^∞ a_F(n) n^-s = exp(∑_{n=2}^∞ f(n) / log(n) * n ^ {1/2 - s}) for ℜ(s) > 1
-/
def L
    (exp : ℂ → ℂ) (sum : (ℤ₀ → ℂ) → ℂ) (inv_log : ℤ₀ → ℂ) (pow : ℤ₀ → ℂ → ℂ) (inv_two : ℂ)
    (s : ℂ) (σ1 : ℜ s > 1)
    := exp (sum (λ n, L.f n * inv_log n * pow n (inv_two - s))) -- sum starting from n = 2 ...?

/--
Degree of F
- d_F := 2 * lim_{x → 0^+} xK(x)
-/
def degree (two : ℂ) (lim0 : (ℝ₀ → ℂ) → ℂ)
    := two * lim0 (λ x, x.elem * L.K x)

/--
Analytic ℂonductor of F
- Q_F := e^(-2f(1))
-/
def conductor (exp : ℂ → ℂ) (minus_two : ℂ)
    := exp (minus_two * L.f 1)

/--
F is positive if
- there are at most finitely many z ∈ ℂ with m(z) < 0
-/
def is_positive (finitely_many_negative : (ℂ → ℝ) → Type*)
    := finitely_many_negative L.m

end LDatum --————————————————————————————————————————————————————————————————————————————--
