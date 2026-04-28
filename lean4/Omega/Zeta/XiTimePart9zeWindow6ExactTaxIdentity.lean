import Mathlib

namespace Omega.Zeta

noncomputable section

/-- Collision-square sum of the actual window-6 audited spectrum `(2^8,3^4,4^9)`. -/
def xi_time_part9ze_window6_exact_tax_identity_binCollisionSquareSum : ℕ :=
  8 * 2 ^ 2 + 4 * 3 ^ 2 + 9 * 4 ^ 2

/-- Collision-square sum of the Wulff floor `(4^1,3^20)`. -/
def xi_time_part9ze_window6_exact_tax_identity_wulffCollisionSquareSum : ℕ :=
  1 * 4 ^ 2 + 20 * 3 ^ 2

/-- The normalized collision excess. -/
def xi_time_part9ze_window6_exact_tax_identity_collisionTax : ℚ :=
  (xi_time_part9ze_window6_exact_tax_identity_binCollisionSquareSum -
      xi_time_part9ze_window6_exact_tax_identity_wulffCollisionSquareSum : ℕ) / 64 ^ 2

/-- Log contribution of one fiber of size `n`, expanded only at the sizes used here. -/
def xi_time_part9ze_window6_exact_tax_identity_groupLogContribution (n : ℕ) : ℝ :=
  match n with
  | 2 => Real.log 2
  | 3 => Real.log 2 + Real.log 3
  | 4 => Real.log 2 + Real.log 3 + Real.log 4
  | _ => 0

/-- Group-log of the actual spectrum `(2^8,3^4,4^9)`. -/
def xi_time_part9ze_window6_exact_tax_identity_binGroupLog : ℝ :=
  8 * xi_time_part9ze_window6_exact_tax_identity_groupLogContribution 2 +
    4 * xi_time_part9ze_window6_exact_tax_identity_groupLogContribution 3 +
      9 * xi_time_part9ze_window6_exact_tax_identity_groupLogContribution 4

/-- Group-log of the Wulff floor `(4^1,3^20)`. -/
def xi_time_part9ze_window6_exact_tax_identity_wulffGroupLog : ℝ :=
  xi_time_part9ze_window6_exact_tax_identity_groupLogContribution 4 +
    20 * xi_time_part9ze_window6_exact_tax_identity_groupLogContribution 3

/-- Normalized group-log excess. -/
def xi_time_part9ze_window6_exact_tax_identity_normalizedGroupLogTax : ℝ :=
  (xi_time_part9ze_window6_exact_tax_identity_binGroupLog -
    xi_time_part9ze_window6_exact_tax_identity_wulffGroupLog) / 64

/-- The endpoint-kappa excess before closed-form logarithmic compression. -/
def xi_time_part9ze_window6_exact_tax_identity_kappaTaxFromExponents : ℝ :=
  (8 / 64 : ℝ) *
    (2 * Real.log 2 - 6 * Real.log 3 + 4 * Real.log 4)

/-- Paper-facing exact arithmetic and logarithmic audit-tax identities. -/
def xi_time_part9ze_window6_exact_tax_identity_statement : Prop :=
  xi_time_part9ze_window6_exact_tax_identity_binCollisionSquareSum = 212 ∧
    xi_time_part9ze_window6_exact_tax_identity_wulffCollisionSquareSum = 196 ∧
    xi_time_part9ze_window6_exact_tax_identity_collisionTax = (1 / 256 : ℚ) ∧
    xi_time_part9ze_window6_exact_tax_identity_binGroupLog -
        xi_time_part9ze_window6_exact_tax_identity_wulffGroupLog =
      8 * Real.log ((4 : ℝ) / 3) ∧
    xi_time_part9ze_window6_exact_tax_identity_normalizedGroupLogTax =
      (1 / 8 : ℝ) * Real.log ((4 : ℝ) / 3) ∧
    xi_time_part9ze_window6_exact_tax_identity_kappaTaxFromExponents =
      (1 / 4 : ℝ) * Real.log ((32 : ℝ) / 27)

/-- Paper label: `thm:xi-time-part9ze-window6-exact-tax-identity`. -/
theorem paper_xi_time_part9ze_window6_exact_tax_identity :
    xi_time_part9ze_window6_exact_tax_identity_statement := by
  have hlog43 : Real.log ((4 : ℝ) / 3) = Real.log 4 - Real.log 3 := by
    rw [Real.log_div] <;> norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    norm_num
  have hlog27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hlog3227 : Real.log ((32 : ℝ) / 27) = 5 * Real.log 2 - 3 * Real.log 3 := by
    rw [Real.log_div, hlog32, hlog27] <;> norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_time_part9ze_window6_exact_tax_identity_binCollisionSquareSum]
  · norm_num [xi_time_part9ze_window6_exact_tax_identity_wulffCollisionSquareSum]
  · norm_num [xi_time_part9ze_window6_exact_tax_identity_collisionTax,
      xi_time_part9ze_window6_exact_tax_identity_binCollisionSquareSum,
      xi_time_part9ze_window6_exact_tax_identity_wulffCollisionSquareSum]
  · rw [hlog43]
    norm_num [xi_time_part9ze_window6_exact_tax_identity_binGroupLog,
      xi_time_part9ze_window6_exact_tax_identity_wulffGroupLog,
      xi_time_part9ze_window6_exact_tax_identity_groupLogContribution]
    ring
  · unfold xi_time_part9ze_window6_exact_tax_identity_normalizedGroupLogTax
    rw [hlog43]
    norm_num [xi_time_part9ze_window6_exact_tax_identity_binGroupLog,
      xi_time_part9ze_window6_exact_tax_identity_wulffGroupLog,
      xi_time_part9ze_window6_exact_tax_identity_groupLogContribution]
    ring
  · unfold xi_time_part9ze_window6_exact_tax_identity_kappaTaxFromExponents
    rw [hlog4, hlog3227]
    norm_num
    ring

end

end Omega.Zeta
