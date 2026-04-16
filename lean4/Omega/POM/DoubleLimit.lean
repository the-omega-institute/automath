import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.POM

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for exchanging thermodynamic and zero-temperature
    limits in `2026_projection_ontological_mathematics_core_tams`.
    cor:double-limit -/
theorem paper_projection_double_limit {α : Type _}
    (thermodynamicLimit zeroTemperatureLimit endpoint : α)
    (hThermo : thermodynamicLimit = endpoint)
    (hZeroTemp : zeroTemperatureLimit = endpoint) :
    thermodynamicLimit = zeroTemperatureLimit ∧
      thermodynamicLimit = endpoint ∧
      zeroTemperatureLimit = endpoint := by
  exact ⟨hThermo.trans hZeroTemp.symm, hThermo, hZeroTemp⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing rigidity wrapper for the double-limit slope audit: once the `q → ∞` endpoint
    package identifies the `m → ∞` then `q → ∞` branch with `log √φ`, and the fixed-`m`
    `ℓ^q → max` branch identifies the opposite iterated limit with `(1/2) log φ`, the generic
    double-limit wrapper pins both iterated limits to the same value.
    cor:pom-double-limit-rigidity-half-logphi -/
theorem paper_pom_double_limit_rigidity_half_logphi
    (qThenM mThenQ : ℝ)
    (hQThenM : qThenM = Real.log (Real.sqrt Real.goldenRatio))
    (hMThenQ : mThenQ = (1 / 2 : ℝ) * Real.log Real.goldenRatio) :
    qThenM = mThenQ ∧
      qThenM = (1 / 2 : ℝ) * Real.log Real.goldenRatio ∧
      mThenQ = (1 / 2 : ℝ) * Real.log Real.goldenRatio := by
  have hhalf :
      Real.log (Real.sqrt Real.goldenRatio) = (1 / 2 : ℝ) * Real.log Real.goldenRatio := by
    rw [Real.log_sqrt (le_of_lt Real.goldenRatio_pos)]
    ring
  have hQEndpoint : qThenM = (1 / 2 : ℝ) * Real.log Real.goldenRatio := hQThenM.trans hhalf
  exact
    paper_projection_double_limit qThenM mThenQ ((1 / 2 : ℝ) * Real.log Real.goldenRatio)
      hQEndpoint hMThenQ

end Omega.POM
