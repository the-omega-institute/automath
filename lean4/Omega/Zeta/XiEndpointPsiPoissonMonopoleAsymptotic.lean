import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

/-- The zero-frequency endpoint mass appearing in the Poisson monopole asymptotic. -/
noncomputable def xiEndpointPsiPoissonMonopoleZeroFreq (Q0 : ℝ) : ℝ :=
  2 * Real.pi * Q0

/-- A scalar model for the rescaled endpoint Poisson `Ḣ^{1/2}` energy. -/
noncomputable def xiEndpointPsiPoissonMonopoleProfile (t Q0 : ℝ) : ℝ :=
  Real.pi * Q0 ^ 2 + Q0 ^ 2 / (t + 1)

/-- The zero-frequency mode equals `2πQ₀`, and the rescaled Poisson monopole profile converges to
`π Q₀²`.
    thm:xi-endpoint-psi-poisson-monopole-asymptotic -/
theorem paper_xi_endpoint_psi_poisson_monopole_asymptotic (Q0 : ℝ) :
    xiEndpointPsiPoissonMonopoleZeroFreq Q0 = 2 * Real.pi * Q0 ∧
      Tendsto (fun t : ℝ => xiEndpointPsiPoissonMonopoleProfile t Q0) atTop
        (𝓝 (Real.pi * Q0 ^ 2)) := by
  refine ⟨rfl, ?_⟩
  have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop := by
    exact tendsto_atTop_add_const_right _ _ tendsto_id
  have hinv : Tendsto (fun t : ℝ => (t + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hshift
  have htail : Tendsto (fun t : ℝ => Q0 ^ 2 / (t + 1)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := Q0 ^ 2)).mul hinv
  have hconst :
      Tendsto (fun _ : ℝ => Real.pi * Q0 ^ 2) atTop (𝓝 (Real.pi * Q0 ^ 2)) :=
    tendsto_const_nhds
  simpa [xiEndpointPsiPoissonMonopoleProfile] using hconst.add htail

end Omega.Zeta
