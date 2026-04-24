import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.EA

/-- Finite-state growth data for the additive/multiplicative energy complementarity inequality. The
scalar fields record the exponential growth rates and the strict Perron gap. -/
structure EnergyComplementarityData where
  alpha : ℝ
  betaAdd : ℝ
  betaMul : ℝ
  kappa : ℝ
  alpha_pos : 0 < alpha
  betaAdd_pos : 0 < betaAdd
  betaMul_pos : 0 < betaMul
  jointGap :
    betaAdd * betaMul ≤ alpha ^ (6 : ℕ) * Real.exp (-kappa)

/-- The logarithmic form of the additive/multiplicative energy complementarity inequality. -/
def EnergyComplementarityConclusion (D : EnergyComplementarityData) : Prop :=
  Real.log D.betaAdd + Real.log D.betaMul ≤ 6 * Real.log D.alpha - D.kappa

/-- The strict Perron-gap hypothesis on the joint synchronous collision graph converts directly into
the logarithmic energy-complementarity inequality after taking logs of the compiled growth rates.
    thm:conclusion72-energy-complementarity -/
theorem paper_conclusion72_energy_complementarity (D : EnergyComplementarityData) :
    EnergyComplementarityConclusion D := by
  unfold EnergyComplementarityConclusion
  have hprod_pos : 0 < D.betaAdd * D.betaMul := mul_pos D.betaAdd_pos D.betaMul_pos
  have hlog :
      Real.log (D.betaAdd * D.betaMul) ≤ Real.log (D.alpha ^ (6 : ℕ) * Real.exp (-D.kappa)) := by
    exact Real.log_le_log hprod_pos D.jointGap
  rw [Real.log_mul D.betaAdd_pos.ne' D.betaMul_pos.ne'] at hlog
  rw [Real.log_mul (pow_ne_zero _ D.alpha_pos.ne') (Real.exp_ne_zero _)] at hlog
  have hpowlog : Real.log (D.alpha ^ (6 : ℕ)) = 6 * Real.log D.alpha := by
    simpa using (Real.log_rpow D.alpha_pos (6 : ℝ))
  calc
    Real.log D.betaAdd + Real.log D.betaMul
        ≤ Real.log (D.alpha ^ (6 : ℕ)) + Real.log (Real.exp (-D.kappa)) := hlog
    _ = 6 * Real.log D.alpha - D.kappa := by rw [hpowlog, Real.log_exp]; ring

end Omega.EA
