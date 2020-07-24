/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    selberg.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
| @source:  arXiv:1308.3067v2 [math.NT] 13 Feb 2015                           |
\- ------------------------------------------------------------------------- -/

import .analysis
import .asymptotic
import .complex
import .reduction

/-!
# Selberg Class

...
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {ℂ : Type*} [DifferenceAlgebra ℂ] {ℭ : Complex ℂ}

local notation `ℝ` := membership ℭ.real
local notation `ℤ` := membership ℭ.int
local notation `ℜ` := ℭ.Re
local notation `ℑ` := ℭ.Im
local notation `ℝ₀` := ℭ.ℝzero
local notation `ℤ₀` := ℭ.ℤzero
local notation `ℝ₀⁺` := ℭ.ℝpos
local notation `ℤ₀⁺` := ℭ.ℤpos
local notation `exp` := ℭ.exp.exp
local notation `log` := ℭ.exp.log
local notation `pow` := ℭ.exp.pow
local notation `|` z `|` := ℭ.abs z
local notation `⌊` z `⌋` := ℭ.floor z

variables {has_limit_at_0    : 𝒫 (ℝ₀⁺ → ℂ)}
          (lim0              : Reduction has_limit_at_0)
          (is_discrete       : 𝒫 (ℂ → Sort))
          {support_summable  : (ℂ → Prop) → 𝒫 (ℂ → ℂ)}
          (support_sum       : Π 𝔇, Reduction (support_summable 𝔇))
          (finitely_many     : 𝒫 (ℂ → Sort))
          (is_smooth_ℝℂ      : 𝒫 (ℝ → ℂ))
          (is_compact        : 𝒫 (ℝ → Sort))
          (fourier_transform : (ℝ → ℂ) → (ℂ → ℂ))
          {ℝpos_integrable   : 𝒫 (ℝ₀⁺ → ℂ)}
          (Intℝpos           : Reduction ℝpos_integrable)
          {ℤpos_summable     : 𝒫 (ℤ₀⁺ → ℂ)}
          (Sumℤpos           : ℤ₀⁺ → Reduction ℤpos_summable)

namespace LDatum --——————————————————————————————————————————————————————————————————————--

/--
A1:
- f(1) ∈ ℝ
- ∀k > 0, f(n) * log^k n <<_k 1
- ∀ε > 0, ∑_{n ≤ x}|f(n)|^2 <<_ε x^ε
-/
structure Axiom1 /-FIXME: [has_bigO (ℤ₀⁺ → ℂ)] [has_bigO (ℂ → ℂ)]-/ (f : ℤ₀⁺ → ℂ)
    := (bounded     : ℂ → (ℤ₀⁺ → ℂ) → (ℂ → ℂ) → Type*)
       (real_at_one : ℭ.is_real (f 1))
       -- (log_bound   : Π k : ℤ₀⁺, (λ n, f n * pow (log n) k) ≪ ↓1)
       -- (sum_bound   : Π ε : ℝ₀⁺, (λ x, /-FIXME:-/ 0) ≪ (λ x, pow x ε))

/--
-/
def scaled_kernel (K : ℝ₀⁺ → ℂ)
    := λ x : ℝ₀⁺, x.elem * K x

/--
-/
def scaled_kernel_has_limit (K : ℝ₀⁺ → ℂ)
    := has_limit_at_0 (scaled_kernel K)

/--
-/
def kernel_degree (K : ℝ₀⁺ → ℂ) (has_limit : scaled_kernel_has_limit K)
    := 2 * lim0.reduce _ has_limit

/--
A2:
- x*K(x) extends to a Schwartz function on ℝ
- lim_{x→0^+}(x * K(x)) ∈ ℝ
-/
structure Axiom2 (K : ℝ₀⁺ → ℂ)
    := (schwartz_extension        : extends_to_schwartz (scaled_kernel K) ℭ.is_real)
       (limit_at_zero_convergence : scaled_kernel_has_limit K)
       (real_degree               : kernel_degree lim0 K limit_at_zero_convergence ~ ℭ.real)

local notation `abs_ℜ_le` T := λ z, |ℜ z| ≤ T

/--
A3:
- supp(m) := { z ∈ ℂ | m (z) ≠ 0 } is discrete(?) and contained in a horizontal strip
    { z ∈ ℂ | |ℑ(z)| ≤ y} for some y ≥ 0
- ∑_{z ∈ supp(m), |ℜ(z)| ≤ T} |m(z)| << 1 + T^A for some A ≥ 0
- #{z ∈ supp(m) | m(z) ∉ ℤ} < ∞
-/
structure Axiom3 (m : ℂ → ℝ)
    := (discrete_support       : is_discrete (supp m))
       (horizontal_support     : ∃ y ≥ 0, Π z, supp m z → |ℑ z| ≤ y)
       (support_sum_converges  : Π T, support_summable (abs_ℜ_le T) (λ z, ℭ.abs (m z)))
       (temp_                  : Π T, (support_sum _).reduce _ (support_sum_converges T) = 0)
       (support_sum_bound      : empty) -- FIXME: ∃ A ≥ (0 : ℝ), (λ T, 0) ≪ (λ T, 1 + pow T A))
       (finite_non_int_support : finitely_many (λ z, supp m z ∧ ¬(m z ~ ℭ.int)))

/--
-/
structure axiom4_property (f : ℤ₀⁺ → ℂ) (K : ℝ₀⁺ → ℂ) (m : ℂ → ℝ) (g : ℝ → ℂ)
    := (smooth                    :  is_smooth_ℝℂ g)
       (compact_support           :  is_compact (supp g))
       (transform                 := fourier_transform g)
       (transform_real_on_reals   :  Π r : ℝ, transform r ~ ℭ.real)
       (support_sum_converges     :  support_summable (λ z, true) (λ z, m z * transform z))
       (kernel_integral_converges :  ℝpos_integrable (λ x, K x * (g 0 - g x.to_membership)))
       (sum_converges             :  ℤpos_summable (λ n, f n * g (ℭ.abs (log n))))
       (fourier_equality          :  (support_sum _).reduce _ support_sum_converges
                                  =  2 * ℜ (Intℝpos.reduce _ kernel_integral_converges
                                                - (Sumℤpos 1).reduce _ sum_converges))

/--
A4:
- ∀ smooth g : ℝ → ℂ of compact support and Fourier Transform h(z) = ∫_ℝ g(x)e^{ixz}dx
    satisfying h(ℝ) ⊆ ℝ, we have the equality:
        ∑_{z∈supp(m)}m(z)h(z) = 2*ℜ( ∫_0^∞ K(x)(g(0) - g(x))dx - ∑_{n=1}^∞ f(n)g(log n) )
-/
structure Axiom4 (f : ℤ₀⁺ → ℂ) (K : ℝ₀⁺ → ℂ) (m : ℂ → ℝ)
    := (property : Π g, axiom4_property
                            support_sum is_smooth_ℝℂ is_compact fourier_transform
                                Intℝpos Sumℤpos f K m g)

end LDatum --————————————————————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables (ℭ)
include ℭ

/--
-/
structure LDatum
    := (f      : ℤ₀⁺ → ℂ)
       (K      : ℝ₀⁺ → ℂ)
       (m      : ℂ   → ℝ)
       (axiom1 : LDatum.Axiom1 f)
       (axiom2 : LDatum.Axiom2 lim0 K)
       (axiom3 : LDatum.Axiom3 is_discrete support_sum finitely_many m)
       (axiom4 : LDatum.Axiom4 support_sum is_smooth_ℝℂ is_compact fourier_transform Intℝpos Sumℤpos f K m)

omit ℭ
variables {ℭ}
--———————————————————————————————————————————————————————————————————————————————————————--

namespace LDatum --——————————————————————————————————————————————————————————————————————--
variables (F : LDatum ℭ
                lim0 is_discrete support_sum finitely_many
                    is_smooth_ℝℂ is_compact fourier_transform Intℝpos Sumℤpos)
          (sum : ℕ → (ℤ₀⁺ → ℂ) → ℂ)

/--
L-Function
- L_F(s) := ∑_{n=1}^∞ a_F(n) n^-s = exp(∑_{n=2}^∞ f(n) / log(n) * n ^ {1/2 - s}) for ℜ(s) > 1
-/
def L_exp_form (s : ℂ) (σ₁ : ℜ s > 1)
    := exp (sum 2 (λ n, F.f n / log n * pow n (2⁻¹ - s)))

/--
-/
def L_character_convergence_criterion (s : ℂ) (σ₁ : ℜ s > 1)
    := empty

/--
-/
def L : LFunction (Sumℤpos 1) (λ b, pow b) := {
    character :=
        begin
            repeat {sorry},
        end,
    continuation := {
        domain := sorry,
        extension := sorry,
        map := sorry,
    }}

/--
Degree of F
- d_F := 2 * lim_{x → 0^+} xK(x)
-/
def degree
    := kernel_degree lim0 F.K F.axiom2.limit_at_zero_convergence

/--
Analytic Conductor of F
-/
def conductor
    := exp (-2 * F.f 1)

/--
F is positive if
- there are at most finitely many z ∈ ℂ with m(z) < 0
-/
def is_positive
    := finitely_many (λ z, F.m z < 0)

end LDatum --————————————————————————————————————————————————————————————————————————————--
