import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.POM

open Filter

/-- Paper label: `thm:pom-functorial-kernel-rh-impossibility`.

The formal core used here is the exponential dominance step in the symmetric-power
argument: if the Perron multiplier `rho` is larger than `1` and a non-Perron mode has
positive modulus `eta`, then some finite symmetric lift has the mode
`eta * rho^(b - 1)` above the square-root Perron scale `sqrt (rho^b)`. -/
theorem paper_pom_functorial_kernel_rh_impossibility (rho eta : ℝ) (hrho : 1 < rho)
    (heta : 0 < eta) :
    ∃ b0 : ℕ, 2 ≤ b0 ∧ eta * rho ^ (b0 - 1) > Real.sqrt (rho ^ b0) := by
  have hrho_pos : 0 < rho := lt_trans zero_lt_one hrho
  have htendsto : Tendsto (fun k : ℕ => rho ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hrho
  have heventually : ∀ᶠ k : ℕ in atTop, eta⁻¹ < rho ^ k :=
    htendsto.eventually (eventually_gt_atTop eta⁻¹)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp heventually
  refine ⟨2 * K + 2, by omega, ?_⟩
  have hbig : 1 < eta * rho ^ K := by
    have hmul := mul_lt_mul_of_pos_left (hK K le_rfl) heta
    simpa [mul_inv_cancel₀ heta.ne'] using hmul
  have hsqrt : Real.sqrt (rho ^ (2 * K + 2)) = rho ^ (K + 1) := by
    have hp : rho ^ (2 * K + 2) = (rho ^ (K + 1)) ^ 2 := by
      rw [show 2 * K + 2 = (K + 1) * 2 by omega, ← pow_mul]
    rw [hp, Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hrho_pos (K + 1))]
  rw [hsqrt]
  calc
    eta * rho ^ (2 * K + 2 - 1) = eta * rho ^ (2 * K + 1) := by
      congr 1
    _ = (eta * rho ^ K) * rho ^ (K + 1) := by
      rw [mul_assoc, ← pow_add]
      congr 1
      ring
    _ > 1 * rho ^ (K + 1) := by
      exact mul_lt_mul_of_pos_right hbig (pow_pos hrho_pos (K + 1))
    _ = rho ^ (K + 1) := one_mul _

end Omega.POM
