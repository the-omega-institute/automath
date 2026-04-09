import Mathlib.Tactic

namespace Omega.Folding.AutocovarianceSeedValues

/-- Autocovariance closed form: c(k) = (1/8)(1/2)^k + (7/648 + k/108)(-1/2)^k.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
noncomputable def autoCov (k : ℕ) : ℚ :=
  (1 / 8) * (1 / 2) ^ k + (7 / 648 + k / 108) * (-1 / 2) ^ k

/-- Seed: c(1) = 17/324.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem autoCov_one : autoCov 1 = 17 / 324 := by
  simp [autoCov]; ring

/-- Seed: c(2) = 25/648.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem autoCov_two : autoCov 2 = 25 / 648 := by
  simp [autoCov]; ring

/-- Seed: c(3) = 7/648.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem autoCov_three : autoCov 3 = 7 / 648 := by
  simp [autoCov]; ring

/-- Seed: c(4) = 7/648 (analyst gave 41/5184, Lean verifies 7/648).
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem autoCov_four : autoCov 4 = 7 / 648 := by
  simp [autoCov]; ring

/-- Seed: c(5) = 11/5184.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem autoCov_five : autoCov 5 = 11 / 5184 := by
  simp [autoCov]; ring

/-- Paper package: autocovariance seed values.
    prop:fold-gauge-anomaly-covariance-distribution-moment -/
theorem paper_fold_autocovariance_seeds :
    autoCov 1 = 17 / 324 ∧
    autoCov 2 = 25 / 648 ∧
    autoCov 3 = 7 / 648 ∧
    autoCov 4 = 7 / 648 ∧
    autoCov 5 = 11 / 5184 :=
  ⟨autoCov_one, autoCov_two, autoCov_three, autoCov_four, autoCov_five⟩

end Omega.Folding.AutocovarianceSeedValues
