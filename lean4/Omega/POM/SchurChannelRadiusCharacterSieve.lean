import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Filter

namespace Omega.POM

/-- Paper label: `thm:pom-schur-channel-radius-character-sieve`. If the same normalized
spectral trace has the pressure limit `P_lambda` and the spectral-radius limit `log rho`, then
`rho = exp P_lambda`, and the square-root threshold is the exponential rewrite of
`2 P_lambda ≤ P_q`. -/
theorem paper_pom_schur_channel_radius_character_sieve (T : ℕ → ℝ) (rho Plambda Pq : ℝ)
    (hrho : 0 < rho)
    (htrace : Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ)) * Real.log |T m|)
      Filter.atTop (nhds Plambda))
    (hspectral : Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ)) * Real.log |T m|)
      Filter.atTop (nhds (Real.log rho))) :
    rho = Real.exp Plambda ∧ (2 * Plambda ≤ Pq ↔ rho ^ 2 ≤ Real.exp Pq) := by
  have hlimit : Plambda = Real.log rho := tendsto_nhds_unique htrace hspectral
  constructor
  · calc
      rho = Real.exp (Real.log rho) := (Real.exp_log hrho).symm
      _ = Real.exp Plambda := by rw [← hlimit]
  · have hexp_two : Real.exp (2 * Plambda) = rho ^ 2 := by
      calc
        Real.exp (2 * Plambda) = Real.exp (Real.log rho + Real.log rho) := by
          rw [hlimit]
          ring_nf
        _ = Real.exp (Real.log rho) * Real.exp (Real.log rho) := Real.exp_add _ _
        _ = rho ^ 2 := by
          rw [Real.exp_log hrho]
          ring
    constructor
    · intro h
      rw [← hexp_two]
      exact Real.exp_le_exp.mpr h
    · intro h
      exact Real.exp_le_exp.mp (by simpa [hexp_two] using h)

end Omega.POM
