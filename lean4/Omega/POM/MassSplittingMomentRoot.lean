import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Omega.POM.MassSplittingMomentRoot

open Real

/-- Power-sum contribution: `M · (ε/M)^q = ε^q · M^(1-q)`.
    prop:pom-mass-splitting-moment-root-transform -/
theorem split_power_contribution (ε : ℝ) (q : ℝ) (M : ℕ)
    (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    (M : ℝ) * ((ε / M) ^ q) = ε ^ q * (M : ℝ) ^ (1 - q) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
  rw [Real.div_rpow hε hMR.le]
  rw [Real.rpow_sub hMR, Real.rpow_one]
  field_simp

/-- Square-root contribution: `M · √(ε/M) = √ε · √M`.
    prop:pom-mass-splitting-moment-root-transform -/
theorem split_sqrt_contribution (ε : ℝ) (M : ℕ) (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    (M : ℝ) * Real.sqrt (ε / M) = Real.sqrt ε * Real.sqrt (M : ℝ) := by
  have hMR : (0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.zero_le M)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)
  rw [Real.sqrt_div hε]
  have hsqrt_M : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hMR
  have hsqrt_M_ne : Real.sqrt (M : ℝ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsqrt_M
    exact (ne_of_gt hMpos) hsqrt_M.symm
  rw [← mul_div_assoc, div_eq_iff hsqrt_M_ne]
  have : Real.sqrt ε * Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = Real.sqrt ε * (M : ℝ) := by
    rw [mul_assoc, hsqrt_M]
  linarith [this]

/-- Power-sum difference: `M·(ε/M)^q - ε^q = ε^q · (M^(1-q) - 1)`.
    prop:pom-mass-splitting-moment-root-transform -/
theorem power_sum_diff (ε : ℝ) (q : ℝ) (M : ℕ)
    (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    (M : ℝ) * (ε / M) ^ q - ε ^ q = ε ^ q * ((M : ℝ) ^ (1 - q) - 1) := by
  have h := split_power_contribution ε q M hε hM
  linarith [h]

/-- Square-root difference: `M·√(ε/M) - √ε = √ε · (√M - 1)`.
    prop:pom-mass-splitting-moment-root-transform -/
theorem sqrt_diff (ε : ℝ) (M : ℕ) (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    (M : ℝ) * Real.sqrt (ε / M) - Real.sqrt ε =
      Real.sqrt ε * (Real.sqrt (M : ℝ) - 1) := by
  have h := split_sqrt_contribution ε M hε hM
  linarith [h]

/-- Package-level power-sum identity with remaining mass.
    prop:pom-mass-splitting-moment-root-transform -/
theorem mass_splitting_power_sum_identity (rest : ℝ) (ε : ℝ) (q : ℝ) (M : ℕ)
    (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    rest + (M : ℝ) * (ε / M) ^ q =
      (rest + ε ^ q) + ε ^ q * ((M : ℝ) ^ (1 - q) - 1) := by
  have h := power_sum_diff ε q M hε hM
  linarith

/-- Package-level sqrt identity with remaining mass.
    prop:pom-mass-splitting-moment-root-transform -/
theorem mass_splitting_sqrt_identity (rest : ℝ) (ε : ℝ) (M : ℕ)
    (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    rest + (M : ℝ) * Real.sqrt (ε / M) =
      (rest + Real.sqrt ε) + Real.sqrt ε * (Real.sqrt (M : ℝ) - 1) := by
  have h := sqrt_diff ε M hε hM
  linarith

/-- Paper package: POM mass-splitting moment-root transform.
    prop:pom-mass-splitting-moment-root-transform -/
theorem paper_pom_mass_splitting_moment_root_transform
    (ε : ℝ) (q : ℝ) (M : ℕ) (hε : 0 ≤ ε) (hM : 1 ≤ M) :
    ((M : ℝ) * (ε / M) ^ q - ε ^ q = ε ^ q * ((M : ℝ) ^ (1 - q) - 1)) ∧
    ((M : ℝ) * Real.sqrt (ε / M) - Real.sqrt ε =
      Real.sqrt ε * (Real.sqrt (M : ℝ) - 1)) :=
  ⟨power_sum_diff ε q M hε hM, sqrt_diff ε M hε hM⟩

end Omega.POM.MassSplittingMomentRoot
