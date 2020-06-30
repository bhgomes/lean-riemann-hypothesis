/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    selberg.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
| @source:  arXiv:1308.3067v2 [math.NT] 13 Feb 2015                           |
\- ------------------------------------------------------------------------- -/

import .analysis
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

/--
-/
def lim0 {X Y} : (X → Y) → Y
    := sorry --! Reduction

/--
-/
def extends_to_schwartz {X Y} : (X → Y) → 𝒫 Y → Type*
    := sorry

/--
-/
def is_discrete {X : Type*} : 𝒫 X → Type*
    := sorry

/--
-/
def has_bounded_count {X : Type*} : 𝒫 X → Type*
    := sorry

/--
-/
def is_smooth {X Y} : (X → Y) → Type*
    := sorry

/--
-/
def is_compact {X : Type*} : 𝒫 X → Type*
    := sorry

/--
-/
def fourier_transform {X Y} : (X → Y) → (Y → Y)
    := sorry

end analysis --——————————————————————————————————————————————————————————————————————————--

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

namespace LDatum --——————————————————————————————————————————————————————————————————————--

/--
A1:
- f(1) ∈ ℝ
- ∀k > 0, f(n) * log^k n <<_k 1
- ∀ε > 0, ∑_{n ≤ x}|f(n)|^2 <<_ε x^ε
-/
structure Axiom1 (f : ℤ₀⁺ → ℂ)
    := (bounded     : ℂ → (ℤ₀⁺ → ℂ) → (ℂ → ℂ) → Type*)
       (real_at_one : ℭ.is_real (f 1))
       (log_bound   : Π k : ℤ₀⁺, bounded k (λ n, f n * pow (log n) k) 1)
       (sum_bound   : empty)

/--
-/
def K_scaled (K : ℝ₀⁺ → ℂ)
    := λ x : ℝ₀⁺, x.elem * K x

/--
A2:
- x*K(x) extends to a Schwartz function on ℝ
- lim_{x→0^+}(x * K(x)) ∈ ℝ
-/
structure Axiom2 (K : ℝ₀⁺ → ℂ)
    := (schwartz_extension : extends_to_schwartz (K_scaled K) ℭ.is_real)
       (real_limit         : ℭ.is_real (lim0 (K_scaled K)))

/--
A3:
- supp(m) := { z ∈ ℂ | m (z) ≠ 0 } is discrete(?) and contained in a horizontal strip
    { z ∈ ℂ | |ℑ(z)| ≤ y} for some y ≥ 0
- ∑_{z ∈ supp(m), |ℜ(z)| ≤ T} |m(z)| << 1 + T^A for some A ≥ 0
- #{z ∈ supp(m) | m(z) ∉ ℤ} < ∞
-/
structure Axiom3 (m : ℂ → ℝ)
    := (discrete_support       : is_discrete (supp m))
       (horizontal_support     : ∃ y ≥ 0, (Π z, supp m z → |ℑ z| ≤ y))
       (support_sum_bound      : empty)
       (finite_non_int_support : has_bounded_count (λ z, supp m z ∧ ¬(m z ~ ℭ.int)))

/--
A4:
- ∀ smooth g : ℝ → ℂ of compact support and Fourier Transform h(z) = ∫_ℝ g(x)e^{ixz}dx
    satisfying h(ℝ) ⊆ ℝ, we have the equality:
        ∑_{z∈supp(m)}m(z)h(z) = 2*ℜ( ∫_0^∞ K(x)(g(0) - g(x))dx - ∑_{n=1}^∞ f(n)g(log n) )
-/
structure Axiom4 (f : ℤ₀⁺ → ℂ) (K : ℝ₀⁺ → ℂ) (m : ℂ → ℝ)
    := (special_equality : Type*)
       (fourier_equality : Π (g : ℝ → ℂ) {_ : is_smooth g} {_ : is_compact (supp g)}, special_equality)

end LDatum --————————————————————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables (ℭ)
include ℭ

/--
-/
structure LDatum
    := (f  : ℤ₀⁺ → ℂ)
       (K  : ℝ₀⁺ → ℂ)
       (m  : ℂ   → ℝ)
       (a1 : LDatum.Axiom1 f)
       (a2 : LDatum.Axiom2 K)
       (a3 : LDatum.Axiom3 m)
       (a4 : LDatum.Axiom4 f K m)

omit ℭ
variables {ℭ}
--———————————————————————————————————————————————————————————————————————————————————————--

namespace LDatum --——————————————————————————————————————————————————————————————————————--
variables (F : LDatum ℭ)
          --! (summable_sequences : 𝒫 (ℤ₀⁺ → ℂ))
          --! (sum : Reduction summable_sequences)
          (sum : ℕ → (ℤ₀⁺ → ℂ) → ℂ)

/--
L-Function
- L_F(s) := ∑_{n=1}^∞ a_F(n) n^-s = exp(∑_{n=2}^∞ f(n) / log(n) * n ^ {1/2 - s}) for ℜ(s) > 1
-/
def L (s : ℂ) (σ₁ : ℜ s > 1)
    := exp (sum 2 (λ n, F.f n / log n * pow n (2⁻¹ - s)))

/--
Degree of F
- d_F := 2 * lim_{x → 0^+} xK(x)
-/
def degree
    := 2 * lim0 (LDatum.K_scaled F.K)

/--
Analytic Conductor of F
-/
def conductor
    := exp (-2 * F.f 1)

/--
F is positive if
- there are at most finitely many z ∈ ℂ with m(z) < 0
-/
def is_positive (finitely_many_negative : (ℂ → ℝ) → Type*)
    := finitely_many_negative F.m

end LDatum --————————————————————————————————————————————————————————————————————————————--
