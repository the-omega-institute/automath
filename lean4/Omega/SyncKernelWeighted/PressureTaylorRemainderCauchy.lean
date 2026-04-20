import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- Cauchy-type tail bound for the pressure Taylor remainder: a coefficient estimate at radius
`r` controls the order-`9` tail by a geometric series in `|x| / r`.
    cor:pressure-taylor-remainder-cauchy -/
theorem paper_pressure_taylor_remainder_cauchy (a : ℕ → ℝ) (M_r r : ℝ) (hr : 0 < r)
    (hcoeff : ∀ n : ℕ, |a (n + 9)| ≤ M_r / r ^ (n + 9)) :
    ∀ x : ℝ, |x| < r →
      |∑' n : ℕ, a (n + 9) * x ^ (n + 9)| ≤
        M_r * (|x| ^ 9 / r ^ 9) * (1 / (1 - |x| / r)) := by
  intro x hx
  set q : ℝ := |x| / r
  have hM_nonneg : 0 ≤ M_r := by
    have h0 : 0 ≤ M_r / r ^ 9 := by
      exact le_trans (by positivity : 0 ≤ |a (0 + 9)|) (by simpa using hcoeff 0)
    have hr9_pos : 0 < r ^ 9 := pow_pos hr 9
    by_contra hM_nonneg'
    have hM_neg : M_r < 0 := lt_of_not_ge hM_nonneg'
    have hneg_div : M_r / r ^ 9 < 0 := div_neg_of_neg_of_pos hM_neg hr9_pos
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (abs_nonneg x) hr.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact (div_lt_one hr).2 hx
  have hmajorant_summable : Summable (fun n : ℕ ↦ M_r * q ^ (n + 9)) := by
    have hgeom : Summable (fun n : ℕ ↦ q ^ n) := summable_geometric_of_lt_one hq_nonneg hq_lt_one
    convert hgeom.mul_left (M_r * q ^ 9) using 1
    ext n
    rw [pow_add]
    ring
  have habs_bound : ∀ n : ℕ, |a (n + 9) * x ^ (n + 9)| ≤ M_r * q ^ (n + 9) := by
    intro n
    have hxpow_nonneg : 0 ≤ |x| ^ (n + 9) := pow_nonneg (abs_nonneg x) _
    calc
      |a (n + 9) * x ^ (n + 9)| = |a (n + 9)| * |x| ^ (n + 9) := by rw [abs_mul, abs_pow]
      _ ≤ (M_r / r ^ (n + 9)) * |x| ^ (n + 9) := by
        exact mul_le_mul_of_nonneg_right (hcoeff n) hxpow_nonneg
      _ = M_r * (|x| ^ (n + 9) / r ^ (n + 9)) := by ring
      _ = M_r * (|x| / r) ^ (n + 9) := by rw [div_pow]
      _ = M_r * q ^ (n + 9) := by simp [q]
  have habs_summable : Summable (fun n : ℕ ↦ |a (n + 9) * x ^ (n + 9)|) :=
    Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) habs_bound hmajorant_summable
  have htsum_le :
      (∑' n : ℕ, |a (n + 9) * x ^ (n + 9)|) ≤ ∑' n : ℕ, M_r * q ^ (n + 9) :=
    Summable.tsum_le_tsum habs_bound habs_summable hmajorant_summable
  have hmajorant_tsum :
      (∑' n : ℕ, M_r * q ^ (n + 9)) =
        M_r * (|x| ^ 9 / r ^ 9) * (1 / (1 - |x| / r)) := by
    calc
      (∑' n : ℕ, M_r * q ^ (n + 9))
          = ∑' n : ℕ, (M_r * q ^ 9) * q ^ n := by
              congr with n
              rw [pow_add]
              ring
      _ = (M_r * q ^ 9) * ∑' n : ℕ, q ^ n := by rw [tsum_mul_left]
      _ = (M_r * q ^ 9) * (1 / (1 - q)) := by
            rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one, inv_eq_one_div]
      _ = M_r * ((|x| / r) ^ 9) * (1 / (1 - |x| / r)) := by simp [q]
      _ = M_r * (|x| ^ 9 / r ^ 9) * (1 / (1 - |x| / r)) := by rw [div_pow]
  calc
    |∑' n : ℕ, a (n + 9) * x ^ (n + 9)| = ‖∑' n : ℕ, a (n + 9) * x ^ (n + 9)‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖a (n + 9) * x ^ (n + 9)‖ := norm_tsum_le_tsum_norm habs_summable
    _ = ∑' n : ℕ, |a (n + 9) * x ^ (n + 9)| := by
      congr with n
    _ ≤ ∑' n : ℕ, M_r * q ^ (n + 9) := htsum_le
    _ = M_r * (|x| ^ 9 / r ^ 9) * (1 / (1 - |x| / r)) := hmajorant_tsum

end

end Omega.SyncKernelWeighted
