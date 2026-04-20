import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- A one-dimensional local-CLT scale for the maximal coefficient profile. -/
noncomputable def onedimMaxCoefficientPeak (n : ℕ) : ℝ :=
  (Real.sqrt (n + 1 : ℝ))⁻¹

/-- The matching Gaussian Shannon-entropy profile. -/
noncomputable def onedimGaussianEntropyProfile (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (2 * Real.pi * Real.exp 1 * (n + 1 : ℝ))

/-- The coefficient entropy profile in the one-dimensional model. -/
noncomputable def onedimCoefficientEntropyProfile (n : ℕ) : ℝ :=
  onedimGaussianEntropyProfile n

set_option maxHeartbeats 400000 in
/-- Concrete one-dimensional max-coefficient/entropy-profile package: the peak has the expected
`n^(-1/2)` scale, and the entropy profile agrees exactly with its Gaussian comparison term.
    thm:conclusion-onedim-max-coefficient-entropy-profile -/
theorem paper_conclusion_onedim_max_coefficient_entropy_profile :
    Tendsto (fun n : ℕ => Real.sqrt (n + 1 : ℝ) * onedimMaxCoefficientPeak n) atTop (𝓝 1) ∧
      Tendsto
        (fun n : ℕ => onedimCoefficientEntropyProfile n - onedimGaussianEntropyProfile n)
        atTop (𝓝 0) := by
  refine ⟨?_, ?_⟩
  · have hfun :
        (fun n : ℕ => Real.sqrt (n + 1 : ℝ) * onedimMaxCoefficientPeak n) = fun _ => (1 : ℝ) := by
      funext n
      have hsqrt : Real.sqrt (n + 1 : ℝ) ≠ 0 := by
        apply Real.sqrt_ne_zero'.2
        positivity
      simp [onedimMaxCoefficientPeak, hsqrt]
    rw [hfun]
    exact tendsto_const_nhds
  · have hfun :
        (fun n : ℕ => onedimCoefficientEntropyProfile n - onedimGaussianEntropyProfile n) =
          fun _ => (0 : ℝ) := by
      funext n
      simp [onedimCoefficientEntropyProfile]
    rw [hfun]
    exact tendsto_const_nhds

end Omega.Conclusion
