import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-leyang-cardano-numerator-divisor-visibility`. -/
theorem paper_xi_leyang_cardano_numerator_divisor_visibility {K : Type*} [Field K]
    [CharZero K] (s y u : K) (hs : s ^ 2 = -3)
    (hcurve : u ^ 2 = -y * (y - 1) * (256 * y ^ 3 + 411 * y ^ 2 + 165 * y + 32)) :
    (let A : K := 128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16;
      (A - 3 * s * u) * (A + 3 * s * u) = 256 * (2 * y + 1) ^ 6 ∧
        ((A - 3 * s * u = 0 ∨ A + 3 * s * u = 0) → 2 * y + 1 = 0)) := by
  let A : K := 128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16
  change (A - 3 * s * u) * (A + 3 * s * u) = 256 * (2 * y + 1) ^ 6 ∧
    ((A - 3 * s * u = 0 ∨ A + 3 * s * u = 0) → 2 * y + 1 = 0)
  have hprod :
      (A - 3 * s * u) * (A + 3 * s * u) = 256 * (2 * y + 1) ^ 6 := by
    subst A
    calc
      (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16 - 3 * s * u) *
          (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16 + 3 * s * u)
          = (128 * y ^ 3 + 219 * y ^ 2 + 69 * y + 16) ^ 2 - 9 * s ^ 2 * u ^ 2 := by
            ring
      _ = 256 * (2 * y + 1) ^ 6 := by
        rw [hcurve, hs]
        ring
  refine ⟨hprod, ?_⟩
  intro hzero
  have hleft : (A - 3 * s * u) * (A + 3 * s * u) = 0 := by
    rcases hzero with hzero | hzero
    · rw [hzero, zero_mul]
    · rw [hzero, mul_zero]
  have hright : (256 : K) * (2 * y + 1) ^ 6 = 0 := by
    simpa [hprod] using hleft
  rcases mul_eq_zero.mp hright with hconst | hpow
  · norm_num at hconst
  · exact eq_zero_of_pow_eq_zero hpow

end Omega.Zeta
