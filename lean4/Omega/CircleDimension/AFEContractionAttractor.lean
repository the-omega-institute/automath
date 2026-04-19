import Mathlib.Tactic
import Omega.CircleDimension.AFEPosteriorSigmaConstraint

namespace Omega.CircleDimension

/-- The contraction/fixed-point envelope around the exact center `1/2`: an approximate fixed
point of `Φ_t` within error `ε`, together with a `q`-contraction about the exact fixed point
`1/2`, forces the standard attractor bound.
    thm:cdim-afe-contraction-attractor -/
theorem paper_cdim_afe_contraction_attractor
    (Phi_t : ℝ → ℝ) (sigma epsilon q : ℝ)
    (hq_lt_one : q < 1)
    (happrox : |sigma - Phi_t sigma| ≤ epsilon)
    (hfixed : Phi_t (1 / 2) = 1 / 2)
    (hcontract : |Phi_t sigma - Phi_t (1 / 2)| ≤ q * |sigma - 1 / 2|) :
    |sigma - 1 / 2| ≤ epsilon / (1 - q) := by
  have hdecomp :
      sigma - 1 / 2 = (sigma - Phi_t sigma) + (Phi_t sigma - Phi_t (1 / 2)) := by
    rw [hfixed]
    ring
  have hstep : |sigma - 1 / 2| ≤ epsilon + q * |sigma - 1 / 2| := by
    calc
      |sigma - 1 / 2| = |(sigma - Phi_t sigma) + (Phi_t sigma - Phi_t (1 / 2))| := by
        rw [hdecomp]
      _ ≤ |sigma - Phi_t sigma| + |Phi_t sigma - Phi_t (1 / 2)| := abs_add_le _ _
      _ ≤ epsilon + q * |sigma - 1 / 2| := add_le_add happrox hcontract
  have hden_pos : 0 < 1 - q := by linarith
  have heps_nonneg : 0 ≤ epsilon := by
    exact le_trans (abs_nonneg (sigma - Phi_t sigma)) happrox
  apply (le_div_iff₀ hden_pos).2
  nlinarith [hstep, abs_nonneg (sigma - 1 / 2), heps_nonneg]

end Omega.CircleDimension
