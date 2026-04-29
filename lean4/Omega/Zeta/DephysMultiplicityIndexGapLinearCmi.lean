import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

/-- Paper label: `cor:dephys-multiplicity-index-gap-linear-cmi`. The supplied tensorized
index-gap identity rewrites the n-period logarithmic gap as `n * Gamma`, and the conditional
mutual-information lower bound then gives the desired scalar estimate. -/
theorem paper_dephys_multiplicity_index_gap_linear_cmi (n : ℕ)
    (ind1 ind2 ind0 Gamma cmiN : ℝ)
    (hGamma : Gamma = Real.log (ind1 * ind2 / ind0))
    (hTensorGap : Real.log ((ind1 ^ n) * (ind2 ^ n) / (ind0 ^ n)) = (n : ℝ) * Gamma)
    (hIndexCMI : Real.log ((ind1 ^ n) * (ind2 ^ n) / (ind0 ^ n)) ≤ cmiN) :
    (n : ℝ) * Gamma ≤ cmiN := by
  have _ : Gamma = Real.log (ind1 * ind2 / ind0) := hGamma
  simpa [hTensorGap] using hIndexCMI

end Omega.Zeta
