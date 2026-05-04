import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Mellin capacity coefficient after specializing the negative moment identity at `s = 2r - 1`. -/
def xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_mellinCoefficient
    (r : ℕ) (capacityIntegral : ℝ) : ℝ :=
  ((2 * r - 1 : ℕ) : ℝ) * ((2 * r : ℕ) : ℝ) * capacityIntegral

/-- The normalized Stirling--Bernoulli hierarchy coefficient before substituting the Mellin
identity. -/
def xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_stirlingCoefficient
    (r : ℕ) (bernoulli geometricCoefficient : ℝ) : ℝ :=
  bernoulli / ((r : ℝ) ^ 2 * ((2 * r - 1 : ℕ) : ℝ)) * geometricCoefficient

/-- The capacity-integral form of the same coefficient after cancellation. -/
def xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_capacityCoefficient
    (r : ℕ) (bernoulli capacityIntegral : ℝ) : ℝ :=
  (2 * bernoulli) / (r : ℝ) * capacityIntegral

/-- Paper label: `cor:xi-time-part70ab-bernoulli-hierarchy-capacity-interpretation`.
Substituting the negative-moment Mellin identity with `s = 2r - 1` into the
Stirling--Bernoulli coefficient cancels the factor `(2r - 1)(2r)` to leave `2B₂ᵣ/r`
times the capacity integral. -/
theorem paper_xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation
    (r : ℕ) (hr : 1 ≤ r) (bernoulli geometricCoefficient capacityIntegral : ℝ)
    (hmellin :
      geometricCoefficient =
        xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_mellinCoefficient
          r capacityIntegral) :
    geometricCoefficient =
        xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_mellinCoefficient
          r capacityIntegral ∧
      xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_stirlingCoefficient
          r bernoulli geometricCoefficient =
        xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_capacityCoefficient
          r bernoulli capacityIntegral := by
  have hr_ne : (r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hr)
  have hr_sq_ne : (r : ℝ) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 hr_ne
  have hodd_pos : 0 < (2 * r - 1 : ℕ) := by omega
  have hodd_ne : (((2 * r - 1 : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (Nat.ne_of_gt hodd_pos)
  refine ⟨hmellin, ?_⟩
  rw [hmellin]
  unfold xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_mellinCoefficient
    xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_stirlingCoefficient
    xi_time_part70ab_bernoulli_hierarchy_capacity_interpretation_capacityCoefficient
  field_simp [hr_ne, hr_sq_ne, hodd_ne]
  norm_num [Nat.cast_mul]
  ring_nf

end

end Omega.Zeta
