import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.EA.Conclusion72EnergyComplementarity

namespace Omega.EA

private lemma log_nat_pow (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.log (x ^ n) = (n : ℝ) * Real.log x := by
  rw [← Real.rpow_natCast, Real.log_rpow hx]

/-- The sum-product exponential law obtained by combining the Cauchy-Schwarz lower bounds for the
sum/product growth rates with the additive/multiplicative energy complementarity gap. -/
theorem paper_conclusion73_sumproduct_exponential_law
    (alpha betaAdd betaMul sumGrowth prodGrowth kappa : ℝ)
    (hα : 1 < alpha)
    (hβAdd : 0 < betaAdd)
    (hβMul : 0 < betaMul)
    (hSum : 0 < sumGrowth)
    (hProd : 0 < prodGrowth)
    (hAddCS : alpha ^ (4 : ℕ) ≤ betaAdd * sumGrowth)
    (hMulCS : alpha ^ (4 : ℕ) ≤ betaMul * prodGrowth)
    (hGap : betaAdd * betaMul ≤ alpha ^ (6 : ℕ) * Real.exp (-kappa)) :
    Real.rpow alpha (1 + kappa / (2 * Real.log alpha)) ≤ max sumGrowth prodGrowth := by
  let D : EnergyComplementarityData :=
    { alpha := alpha
      betaAdd := betaAdd
      betaMul := betaMul
      kappa := kappa
      alpha_pos := by linarith
      betaAdd_pos := hβAdd
      betaMul_pos := hβMul
      jointGap := hGap }
  have h72 := paper_conclusion72_energy_complementarity D
  have hαpos : 0 < alpha := by linarith
  have hlogαpos : 0 < Real.log alpha := Real.log_pos hα
  have hlogαne : Real.log alpha ≠ 0 := ne_of_gt hlogαpos
  have hAddLog :
      4 * Real.log alpha ≤ Real.log betaAdd + Real.log sumGrowth := by
    have h :=
      Real.log_le_log (show 0 < alpha ^ (4 : ℕ) by positivity) hAddCS
    rw [Real.log_mul hβAdd.ne' hSum.ne', log_nat_pow alpha hαpos 4] at h
    simpa using h
  have hMulLog :
      4 * Real.log alpha ≤ Real.log betaMul + Real.log prodGrowth := by
    have h :=
      Real.log_le_log (show 0 < alpha ^ (4 : ℕ) by positivity) hMulCS
    rw [Real.log_mul hβMul.ne' hProd.ne', log_nat_pow alpha hαpos 4] at h
    simpa using h
  have hGrowthLog :
      2 * Real.log alpha + kappa ≤ Real.log sumGrowth + Real.log prodGrowth := by
    have h72' : Real.log betaAdd + Real.log betaMul ≤ 6 * Real.log alpha - kappa := by
      simpa [D, EnergyComplementarityConclusion] using h72
    linarith
  have hMaxLog :
      Real.log sumGrowth + Real.log prodGrowth ≤ 2 * Real.log (max sumGrowth prodGrowth) := by
    have hSumLe : Real.log sumGrowth ≤ Real.log (max sumGrowth prodGrowth) := by
      apply Real.log_le_log hSum
      exact le_max_left _ _
    have hProdLe : Real.log prodGrowth ≤ Real.log (max sumGrowth prodGrowth) := by
      apply Real.log_le_log hProd
      exact le_max_right _ _
    linarith
  have hTargetLog :
      Real.log (Real.rpow alpha (1 + kappa / (2 * Real.log alpha))) =
        Real.log alpha + kappa / 2 := by
    calc
      Real.log (Real.rpow alpha (1 + kappa / (2 * Real.log alpha))) =
          (1 + kappa / (2 * Real.log alpha)) * Real.log alpha := by
            exact Real.log_rpow hαpos _
      _ = Real.log alpha + kappa / 2 := by
        field_simp [hlogαne]
  have hLog :
      Real.log (Real.rpow alpha (1 + kappa / (2 * Real.log alpha))) ≤
        Real.log (max sumGrowth prodGrowth) := by
    rw [hTargetLog]
    have : 2 * (Real.log alpha + kappa / 2) ≤ 2 * Real.log (max sumGrowth prodGrowth) := by
      linarith
    linarith
  have hTargetPos : 0 < Real.rpow alpha (1 + kappa / (2 * Real.log alpha)) :=
    Real.rpow_pos_of_pos hαpos _
  have hMaxPos : 0 < max sumGrowth prodGrowth := lt_of_lt_of_le hSum (le_max_left _ _)
  have hExp := Real.exp_le_exp.mpr hLog
  rw [Real.exp_log hTargetPos, Real.exp_log hMaxPos] at hExp
  exact hExp

end Omega.EA
