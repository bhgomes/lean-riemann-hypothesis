/- ------------------------------------------------------------------------- -\
| @project: riemann_hypothesis                                                |
| @file:    riemann.lean                                                      |
| @author:  Brandon H. Gomes                                                  |
| @affil:   Rutgers University                                                |
\- ------------------------------------------------------------------------- -/

import .analysis
import .complex

/-!
-/

--———————————————————————————————————————————————————————————————————————————————————————--
variables {ℂ : Type*} [DifferenceAlgebra ℂ] (ℭ : Complex ℂ)
          {summable_series : 𝒫 (ℭ.ℤpos → ℂ)}
          (Sum : Reduction summable_series)

/--
-/
def riemann_hypothesis
    (L             : LFunction Sum (λ b, ℭ.exp.pow b))
    (temp_         : ℭ.is_real 2⁻¹)
    (contains_half : Π {s}, ℭ.Re s ≥ ⟨2⁻¹, temp_⟩ → L.continuation.domain s)
    := Π s {h : ℭ.Re s ≥ ⟨2⁻¹, temp_⟩},
        L.continuation.map s (contains_half h) = 0 ←→ ℭ.Re s = ⟨2⁻¹, temp_⟩
