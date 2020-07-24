/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    complex.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .algebra

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables (ℂ : Type*) [DifferenceAlgebra ℂ]

/--
-/
structure Exp
    := (exp             : ℂ → ℂ)
       (exp_zero_is_one : exp 0 = 1)
       (log             : ℂ → ℂ)
       (exp_log_inverse : Π {z}, exp (log z) = z)

namespace Exp --—————————————————————————————————————————————————————————————————————————--
variables {ℂ} (ℯ : Exp ℂ)

/--
-/
def pow (b z)
    := ℯ.exp (ℯ.log b * z)

/--
-/
instance : has_pow ℂ ℂ
    := ⟨ℯ.pow⟩

/--
-/
def pow_zero_is_one : Π b, ℯ.pow b 0 = 1 :=
    begin
        intros,
        rw pow,
        rw DifferenceAlgebra.zero_right_absorb,
        rw exp_zero_is_one,
    end

end Exp --———————————————————————————————————————————————————————————————————————————————--

/--
-/
structure ComplexBase
    := (real        : ℂ → ℂ)
       (int         : ℂ → ℂ)
       (Real        : HomomorphicProjector real has_sub.sub)
       (Int         : SubProjector int real)
       (real_lt     : membership real → membership real → Prop)
       (zero_is_int : 0 ~ int)
       (one_is_int  : 1 ~ int)

namespace ComplexBase --—————————————————————————————————————————————————————————————————--
variables {ℂ} (ℭ : ComplexBase ℂ)

local notation `ℝ` := membership ℭ.real
local notation `ℤ` := membership ℭ.int

/--
-/
instance real_has_lt : has_lt ℝ
    := ⟨ℭ.real_lt⟩

/--
-/
instance int_has_lt : has_lt ℤ
    := ⟨λ p q, ℭ.Int.lifted p < ℭ.Int.lifted q⟩

/--
-/
instance real_has_zero : has_zero ℝ
    := ⟨⟨0, ℭ.Int.inclusion ℭ.zero_is_int⟩⟩

/--
-/
instance real_has_one : has_one ℝ
    := ⟨⟨1, ℭ.Int.inclusion ℭ.one_is_int⟩⟩

/--
-/
instance int_has_zero : has_zero ℤ
    := membership.has_zero (ℭ.zero_is_int)

/--
-/
instance int_has_one : has_one ℤ
    := membership.has_one (ℭ.one_is_int)

end ComplexBase --———————————————————————————————————————————————————————————————————————--

/--
-/
structure Complex extends ComplexBase ℂ
    := (zero_lt_one : 0 < (1 : membership real))
       (abs_map     : ℂ → ℂ)
       (Abs         : AbsoluteValue Real abs_map)
       (exp         : Exp ℂ)

namespace Complex --—————————————————————————————————————————————————————————————————————--
variables {ℂ} (ℭ : Complex ℂ)

local notation `ℝ` := membership ℭ.real
local notation `ℤ` := membership ℭ.int

/--
-/
def abs
    := ℭ.Abs.to_SubProjector.by_inclusion

/--
-/
instance : has_lt ℂ
    := ⟨λ p q, ℭ.abs p < ℭ.abs q⟩

/--
-/
def is_real (z)
    := z ~ ℭ.real

/--
-/
def Re
    := ℭ.Real.as_member

/--
-/
def imag (z)
    := z - ℭ.real z

/--
-/
def is_imag (z)
    := z ~ ℭ.imag

/--
-/
def Imag : HomomorphicProjector ℭ.imag has_sub.sub := {
    idempotent :=
        begin
            intros,
            repeat { rw imag },
            rw [ℭ.Real.homomorphic,
                ℭ.Real.idempotent,
                DifferenceDomain.sub_cancel,
                DifferenceDomain.sub_right_id],
        end,
    homomorphic :=
        begin
            rw homomorphism,
            intros,
            repeat { rw imag },
            rw [ℭ.Real.homomorphic, DifferenceDomain.sub_inner_swap],
        end }

/--
-/
def Im
    := ℭ.Imag.as_member

/--
-/
def is_int (z)
    := z ~ ℭ.int

/--
-/
def floor
    := ℭ.Int.as_member

/--
-/
structure ℝpos extends ℝ
    := (is_pos : 0 < to_membership)

/--
-/
def ℝpos_one : ℭ.ℝpos
    := ⟨1, ℭ.zero_lt_one⟩

/--
-/
instance ℝpos_has_one : has_one ℭ.ℝpos
    := ⟨ℭ.ℝpos_one⟩

/--
-/
instance ℝpos_elem : has_coe ℭ.ℝpos ℂ
    := ⟨λ z, z.elem⟩

/--
-/
structure ℤpos extends ℤ
    := (is_pos : 0 < to_membership)

/--
-/
def ℤpos_one : ℭ.ℤpos
    := ⟨1, ℭ.zero_lt_one⟩

/--
-/
instance ℤpos_has_one : has_one ℭ.ℤpos
    := ⟨ℭ.ℤpos_one⟩

/--
-/
instance ℤpos_elem : has_coe ℭ.ℤpos ℂ
    := ⟨λ z, z.elem⟩

/--
-/
structure ℝzero extends ℝ
    := (is_ge_zero : 0 ≤ to_membership)

/--
-/
instance ℝzero_has_zero : has_zero ℭ.ℝzero
    := ⟨⟨0, begin repeat {sorry}, end⟩⟩

/--
-/
instance ℝzero_has_one : has_one ℭ.ℝzero
    := ⟨⟨1, begin repeat {sorry}, end⟩⟩

/--
-/
structure ℤzero extends ℤ
    := (is_ge_zero : 0 ≤ to_membership)

/--
-/
instance ℤzero_has_zero : has_zero ℭ.ℤzero
    := ⟨⟨0, begin repeat {sorry}, end⟩⟩

/--
-/
instance ℤzero_has_one : has_one ℭ.ℤzero
    := ⟨⟨1, begin repeat {sorry}, end⟩⟩

end Complex --———————————————————————————————————————————————————————————————————————————--
