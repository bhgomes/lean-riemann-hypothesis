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
variables (ℂ : Type*) [has_one ℂ] [DifferenceDomain ℂ]

/--
-/
structure Complex
    := (real        : ℂ → ℂ)
       (Real        : Projector real)
       (int         : ℂ → ℂ)
       (Int         : Projector int)
       (abs         : ℂ → membership real)
       (int_is_real : Π {z}, z ~ int → z ~ real)
       (zero_is_int : 0 ~ int)
       (one_is_int  : 1 ~ int)
       (real_lt     : membership real → membership real → Prop)
       (zero_lt_one : real_lt ⟨_, int_is_real zero_is_int⟩ ⟨_, int_is_real one_is_int⟩)

namespace Complex --—————————————————————————————————————————————————————————————————————--
variables {ℂ} (ℭ : Complex ℂ)

/--
-/
def is_real (z)
    := z ~ ℭ.real

/--
-/
def is_int (z)
    := z ~ ℭ.int

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
def Imag : Projector ℭ.imag :=
{
    idempotent :=
        begin
            intros,
            repeat { rw imag },
            rw ℭ.Real.respects_sub,
            rw ℭ.Real.idempotent,
            rw DifferenceDomain.sub_cancel,
            rw DifferenceDomain.sub_right_id,
        end,
    respects_sub :=
        begin
            intros,
            repeat { rw imag },
            rw ℭ.Real.respects_sub,
            rw DifferenceDomain.sub_inner_swap,
        end
}

/--
-/
def floor
    := ℭ.Int.member

/--
-/
def Re
    := ℭ.Real.member

/--
-/
def Im
    := ℭ.Imag.member

/--
-/
instance real_has_lt : has_lt (membership ℭ.real)
    := ⟨ℭ.real_lt⟩

/--
-/
def int_as_real (n : membership ℭ.int) : membership ℭ.real
    := ⟨n.elem, ℭ.int_is_real n.is_member⟩

/--
-/
def int_lt (m n : membership ℭ.int)
    := (ℭ.int_as_real m) < (ℭ.int_as_real n)

/--
-/
instance int_has_lt : has_lt (membership ℭ.int)
    := ⟨ℭ.int_lt⟩

/--
-/
def zero_int : membership ℭ.int
    := ⟨0, ℭ.zero_is_int⟩

/--
-/
instance int_has_zero : has_zero (membership ℭ.int)
    := ⟨ℭ.zero_int⟩

/--
-/
def zero_real : membership ℭ.real
    := ⟨0, ℭ.int_is_real ℭ.zero_is_int⟩

/--
-/
instance real_has_zero : has_zero (membership ℭ.real)
    := ⟨ℭ.zero_real⟩

/--
-/
def one_int : membership ℭ.int
    := ⟨1, ℭ.one_is_int⟩

/--
-/
instance int_has_one : has_one (membership ℭ.int)
    := ⟨ℭ.one_int⟩

/--
-/
def one_real : membership ℭ.real
    := ⟨1, ℭ.int_is_real ℭ.one_is_int⟩

/--
-/
instance real_has_one : has_one (membership ℭ.real)
    := ⟨ℭ.one_real⟩

/--
-/
structure ℝpos extends membership ℭ.real
    := (is_pos : ℭ.zero_real < to_membership)

/--
-/
def one_real_pos : ℭ.ℝpos
    := ⟨ℭ.one_real, ℭ.zero_lt_one⟩

/--
-/
instance real_pos_has_one : has_one ℭ.ℝpos
    := ⟨ℭ.one_real_pos⟩

/--
-/
structure ℤpos extends membership ℭ.int
    := (is_pos : ℭ.zero_int < to_membership)

/--
-/
def one_int_pos : ℭ.ℤpos
    := ⟨ℭ.one_int, ℭ.zero_lt_one⟩

/--
-/
instance int_pos_has_one : has_one ℭ.ℤpos
    := ⟨ℭ.one_int_pos⟩

end Complex --———————————————————————————————————————————————————————————————————————————--
