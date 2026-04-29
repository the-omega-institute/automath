import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

open Filter
open scoped Topology

/-- Paper-facing Aitken limit statement: if the two-step ratio sequence converges to `φ`,
the numerator correction converges to `1`, and the Aitken delta is their quotient, then the
delta converges to `φ⁻¹`. -/
def pom_aitken_golden_limit_statement : Prop :=
  ∀ (R_q eta_q delta_ait : ℕ → ℝ),
    Tendsto R_q atTop (𝓝 Real.goldenRatio) →
      Tendsto eta_q atTop (𝓝 1) →
        (∀ q, delta_ait q = eta_q q / R_q q) →
          Tendsto delta_ait atTop (𝓝 (Real.goldenRatio⁻¹))

/-- Paper label: `cor:pom-aitken-golden-limit`. -/
theorem paper_pom_aitken_golden_limit : pom_aitken_golden_limit_statement := by
  intro R_q eta_q delta_ait hR hEta hDelta
  have hRinv : Tendsto (fun q : ℕ => (R_q q)⁻¹) atTop (𝓝 (Real.goldenRatio⁻¹)) :=
    hR.inv₀ Real.goldenRatio_ne_zero
  have hMul :
      Tendsto (fun q : ℕ => eta_q q * (R_q q)⁻¹) atTop
        (𝓝 (1 * Real.goldenRatio⁻¹)) := by
    exact hEta.mul hRinv
  have hEq :
      delta_ait =ᶠ[atTop] fun q : ℕ => eta_q q * (R_q q)⁻¹ := by
    filter_upwards with q
    rw [hDelta q, div_eq_mul_inv]
  simpa using hMul.congr' hEq.symm

end Omega.POM
