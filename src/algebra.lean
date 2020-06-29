/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    algebra.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .basic

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {S : Type*}

/--
-/
def homomorphism (π : S → S) (op : S → S → S)
    := Π p q, π (op p q) = op (π p) (π q)

/--
-/
structure Projector (π : S → S)
    := (idempotent : Π s, π (π s) = π s)

namespace Projector --———————————————————————————————————————————————————————————————————--
variables {π : S → S} (𝔓 : Projector π)

/--
-/
def as_member (s) : membership π
    := ⟨π s, 𝔓.idempotent s⟩

end Projector --—————————————————————————————————————————————————————————————————————————--

/--
-/
structure SubProjector (π : S → S) (β : S → S) extends Projector π
    := (inclusion : Π {s}, s ~ π → s ~ β)

namespace SubProjector --————————————————————————————————————————————————————————————————--
variables {π : S → S} {β : S → S} (𝔖 : SubProjector π β)

/--
-/
def as_member
    := 𝔖.to_Projector.as_member

/--
-/
def inclusion_idempotent (s)
    := 𝔖.inclusion (𝔖.idempotent s)

/--
-/
def by_inclusion (s) : membership β
    := ⟨π s, 𝔖.inclusion_idempotent s⟩

/--
-/
def lifted (z : membership π) : membership β
    := ⟨z.elem, 𝔖.inclusion z.is_member⟩

--———————————————————————————————————————————————————————————————————————————————————————--
include 𝔖

/--
-/
def op_inclusion {op : S → S → S} (h : homomorphism β op) (p q) : membership β
    := ⟨op (π p) (π q),
        begin
            let iip := 𝔖.inclusion_idempotent p,
            let iiq := 𝔖.inclusion_idempotent q,
            rw is_same at *,
            rw [h, iip, iiq],
        end⟩

omit 𝔖
--———————————————————————————————————————————————————————————————————————————————————————--

end SubProjector --——————————————————————————————————————————————————————————————————————--

/--
-/
structure HomomorphicProjector (π : S → S) (op : S → S → S) extends Projector π
    := (homomorphic : homomorphism π op)

namespace HomomorphicProjector --————————————————————————————————————————————————————————--
variables {π : S → S} {op : S → S → S} (ℌ : HomomorphicProjector π op)

/--
-/
def as_member
    := ℌ.to_Projector.as_member

end HomomorphicProjector --——————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables (S)

/--
-/
class DifferenceDomain extends has_zero S, has_sub S
    := (sub_cancel     : Π       s : S, s - s = 0)
       (sub_right_id   : Π       s : S, s - 0 = s)
       (sub_inner_swap : Π a b c d : S, (a - b) - (c - d) = (a - c) - (b - d))
       (sub_outer_swap : Π a b c d : S, (a - b) - (c - d) = (d - b) - (c - a))

namespace DifferenceDomain --————————————————————————————————————————————————————————————--
variables {S} [DifferenceDomain S]

/--
-/
instance : has_neg S
    := ⟨λ s, 0 - s⟩

/--
-/
instance : has_add S
    := ⟨λ x y, x - -y⟩

/--
-/
def sub_right_left_swap (x y z : S) : (x - y) - z = (x - z) - y :=
    begin
        rw ←sub_right_id z,
        rw sub_inner_swap,
        rw sub_right_id,
        rw sub_right_id,
    end

/--
-/
def sub_left_right_swap (x y z : S) : x - (y - z) = z - (y - x) :=
    begin
        rw ←sub_right_id x,
        rw sub_outer_swap,
        rw sub_right_id,
        rw sub_right_id,
    end

end DifferenceDomain --——————————————————————————————————————————————————————————————————--

/--
-/
class DifferenceAlgebra extends has_one S, has_inv S, has_mul S, DifferenceDomain S
    := (one_inv_is_one     : (1 : S)⁻¹ = 1)
       (inv_involution     : Π     s : S, (s⁻¹)⁻¹ = s)
       (mul_right_id       : Π     s : S, s * 1 = s)
       (inv_mul_is_mul_inv : Π   p q : S, (p * q)⁻¹ = p⁻¹ * q⁻¹)
       (left_distrib       : Π x y z : S, x * (y - z) = (x * y) - (x * z))
       (right_distrib      : Π x y z : S, (y - z) * x = (y * x) - (z * x))

namespace DifferenceAlgebra --———————————————————————————————————————————————————————————--
variables {S} [DifferenceAlgebra S]

/--
-/
instance : has_div S
    := ⟨λ x y, x * y⁻¹⟩

/--
-/
def zero_right_absorb (s : S) : s * 0 = 0 :=
    begin
        rw ←DifferenceDomain.sub_cancel s,
        rw left_distrib,
        repeat { rw DifferenceDomain.sub_cancel },
    end

/--
-/
def zero_left_absorb (s : S) : 0 * s = 0 :=
    begin
        rw ←DifferenceDomain.sub_cancel s,
        rw right_distrib,
        repeat { rw DifferenceDomain.sub_cancel },
    end

end DifferenceAlgebra --—————————————————————————————————————————————————————————————————--

--———————————————————————————————————————————————————————————————————————————————————————--
variables {S}

/--
-/
structure AbsoluteValue [has_zero S] [has_sub S] [has_mul S]
    {β : S → S}
    (ℌ : HomomorphicProjector β has_sub.sub)
    [has_zero (membership β)]
    [has_le (membership β)]
    (π : S → S)
    extends SubProjector π β
    := (root_at_zero   : π 0 = 0)
       (multiplicative : homomorphism π (*))
       (positivity     : Π   s, to_SubProjector.by_inclusion s ≥ 0)
       (triangular     : Π p q, to_SubProjector.op_inclusion ℌ.homomorphic p q
                              ≤ to_SubProjector.by_inclusion (p - q))

namespace AbsoluteValue --———————————————————————————————————————————————————————————————--
variables [has_zero S] [has_sub S] [has_mul S]
          {β : S → S}
          {ℌ : HomomorphicProjector β has_sub.sub}
          [has_zero (membership β)]
          [has_le (membership β)]
          {π : S → S} (𝔄 : AbsoluteValue ℌ π)

/--
-/
def as_member
    := 𝔄.to_Projector.as_member

/--
-/
def to_HomomorphicProjector : HomomorphicProjector π (*)
    := ⟨⟨𝔄.to_Projector.idempotent⟩, 𝔄.multiplicative⟩

end AbsoluteValue --—————————————————————————————————————————————————————————————————————--
