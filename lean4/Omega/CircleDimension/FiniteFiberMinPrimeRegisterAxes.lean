import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local data for the finite-fiber minimal-prime-register-axis package. The numeric fields
record the three paper-facing generator counts, while the witness fields package the identifications
between them. -/
structure FiniteFiberMinPrimeRegisterAxesData where
  minGeneratorCount : Nat
  maxFpQuotientDim : Nat
  minPrimeRegisterAxes : Nat
  pcdim : Nat
  minGeneratorCount_eq_maxFpQuotientDim : minGeneratorCount = maxFpQuotientDim
  minPrimeRegisterAxes_eq_minGeneratorCount : minPrimeRegisterAxes = minGeneratorCount
  pcdim_eq_minGeneratorCount : pcdim = minGeneratorCount

/-- Paper-facing wrapper for the finite-fiber generator-count package: the minimal number of
abstract generators agrees with the maximal mod-`p` quotient rank, with the minimal continuous
prime-register axis count, and with the profinite circle dimension.
    prop:cdim-finite-fiber-min-prime-register-axes -/
theorem paper_cdim_finite_fiber_min_prime_register_axes
    (D : FiniteFiberMinPrimeRegisterAxesData) :
    D.minGeneratorCount = D.maxFpQuotientDim ∧
      D.minPrimeRegisterAxes = D.minGeneratorCount ∧
      D.pcdim = D.minGeneratorCount := by
  exact ⟨D.minGeneratorCount_eq_maxFpQuotientDim, D.minPrimeRegisterAxes_eq_minGeneratorCount,
    D.pcdim_eq_minGeneratorCount⟩

end Omega.CircleDimension
