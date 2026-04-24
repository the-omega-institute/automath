import Omega.CircleDimension.CircleDim
import Omega.CircleDimension.FiniteFiberMinPrimeRegisterAxes

namespace Omega.CircleDimension

/-- Paper-facing corollary: finite extensions preserve `circleDim`, and any external register count
`k` dominating the minimal prime-register axis count also dominates the profinite circle
dimension.
    cor:cdim-finite-extension-pro-cdim-lower-bound -/
theorem paper_cdim_finite_extension_pro_cdim_lower_bound
    (freeRank torsionE torsionG k minGeneratorCount maxFpQuotientDim minPrimeRegisterAxes pcdim :
      ℕ)
    (hminGeneratorCount_eq_maxFpQuotientDim : minGeneratorCount = maxFpQuotientDim)
    (hminPrimeRegisterAxes_eq_minGeneratorCount : minPrimeRegisterAxes = minGeneratorCount)
    (hpcdim_eq_minGeneratorCount : pcdim = minGeneratorCount)
    (hk : minPrimeRegisterAxes ≤ k) :
    circleDim freeRank torsionE = circleDim freeRank torsionG ∧ pcdim ≤ k := by
  let D : FiniteFiberMinPrimeRegisterAxesData :=
    { minGeneratorCount := minGeneratorCount
      maxFpQuotientDim := maxFpQuotientDim
      minPrimeRegisterAxes := minPrimeRegisterAxes
      pcdim := pcdim
      minGeneratorCount_eq_maxFpQuotientDim := hminGeneratorCount_eq_maxFpQuotientDim
      minPrimeRegisterAxes_eq_minGeneratorCount := hminPrimeRegisterAxes_eq_minGeneratorCount
      pcdim_eq_minGeneratorCount := hpcdim_eq_minGeneratorCount }
  have hpack := paper_cdim_finite_fiber_min_prime_register_axes D
  refine ⟨circleDim_finite_extension freeRank torsionE torsionG, ?_⟩
  rcases hpack with ⟨_, haxes, hpcdim⟩
  have hpcdim_axes : pcdim = minPrimeRegisterAxes := by
    simpa [D] using hpcdim.trans haxes.symm
  rw [hpcdim_axes]
  exact hk

end Omega.CircleDimension
