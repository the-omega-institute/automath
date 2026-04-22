import Mathlib

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Paper label: `prop:abel-analytic-remainder-decimation-collapse`. -/
theorem paper_abel_analytic_remainder_decimation_collapse (h : ℕ → ℂ) (k : ℕ) (R M : ℝ)
    (hk : 0 < k) (hR : 1 < R) (hM : 0 ≤ M)
    (hbound : ∀ m : ℕ, ‖h m‖ ≤ M * (1 / R) ^ m) :
    ∀ r : ℂ, ‖r‖ ≤ 1 →
      ‖(tsum fun n : ℕ => h (k * n) * r ^ n) - h 0‖ ≤ M * (1 / R) ^ k / (1 - (1 / R) ^ k) := by
  intro r hr
  let f : ℕ → ℂ := fun n => h (k * n) * r ^ n
  let q : ℝ := (1 / R) ^ k
  have hR_pos : 0 < R := lt_trans zero_lt_one hR
  have hinv_nonneg : 0 ≤ 1 / R := by positivity
  have hinv_lt_one : 1 / R < 1 := by
    simpa [one_div] using inv_lt_one_of_one_lt₀ hR
  have hq_nonneg : 0 ≤ q := by
    exact pow_nonneg hinv_nonneg k
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact pow_lt_one₀ hinv_nonneg hinv_lt_one hk.ne'
  have hmajorant_summable : Summable (fun n : ℕ => M * q ^ (n + 1)) := by
    have hgeom : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq_nonneg hq_lt_one
    convert hgeom.mul_left (M * q) using 1
    ext n
    rw [pow_add]
    ring
  have htail_bound : ∀ n : ℕ, ‖f (n + 1)‖ ≤ M * q ^ (n + 1) := by
    intro n
    have hrpow_nonneg : 0 ≤ ‖r‖ ^ (n + 1) := pow_nonneg (norm_nonneg r) _
    have hrpow_le_one : ‖r‖ ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ (norm_nonneg r) hr
    have hcoeff_nonneg : 0 ≤ M * (1 / R) ^ (k * (n + 1)) := by
      exact mul_nonneg hM (pow_nonneg hinv_nonneg _)
    calc
      ‖f (n + 1)‖ = ‖h (k * (n + 1)) * r ^ (n + 1)‖ := by simp [f]
      _ = ‖h (k * (n + 1))‖ * ‖r‖ ^ (n + 1) := by rw [norm_mul, Complex.norm_pow]
      _ ≤ (M * (1 / R) ^ (k * (n + 1))) * ‖r‖ ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right (hbound (k * (n + 1))) hrpow_nonneg
      _ ≤ (M * (1 / R) ^ (k * (n + 1))) * 1 := by
        exact mul_le_mul_of_nonneg_left hrpow_le_one hcoeff_nonneg
      _ = M * q ^ (n + 1) := by
        simp [q, pow_mul]
  have htail_norm_summable : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_bound hmajorant_summable
  have htail_summable : Summable (fun n : ℕ => f (n + 1)) := summable_norm_iff.mp htail_norm_summable
  have hf_bound : ∀ n : ℕ, ‖f n‖ ≤ M * q ^ n := by
    intro n
    cases n with
    | zero =>
        calc
          ‖f 0‖ = ‖h 0‖ := by simp [f]
          _ ≤ M := by simpa using hbound 0
          _ = M * q ^ 0 := by simp
    | succ n =>
        simpa using htail_bound n
  have hnorm_summable : Summable (fun n : ℕ => ‖f n‖) := by
    have hmajorant : Summable (fun n : ℕ => M * q ^ n) := by
      exact (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left M
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf_bound hmajorant
  have hf_summable : Summable f := summable_norm_iff.mp hnorm_summable
  have hsplit : f 0 + ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
    simpa using hf_summable.sum_add_tsum_nat_add 1
  have htail_eq : ∑' n : ℕ, f (n + 1) = (∑' n : ℕ, f n) - h 0 := by
    rw [eq_sub_iff_add_eq]
    simpa [f, add_comm, add_left_comm, add_assoc] using hsplit
  have htail_le :
      ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, M * q ^ (n + 1) := by
    calc
      ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm htail_norm_summable
      _ ≤ ∑' n : ℕ, M * q ^ (n + 1) :=
        Summable.tsum_le_tsum htail_bound htail_norm_summable hmajorant_summable
  have hmajorant_tsum : (∑' n : ℕ, M * q ^ (n + 1)) = M * q / (1 - q) := by
    calc
      (∑' n : ℕ, M * q ^ (n + 1)) = ∑' n : ℕ, (M * q) * q ^ n := by
        congr with n
        rw [pow_add]
        ring
      _ = (M * q) * ∑' n : ℕ, q ^ n := by rw [tsum_mul_left]
      _ = (M * q) * (1 / (1 - q)) := by
        rw [tsum_geometric_of_lt_one hq_nonneg hq_lt_one, inv_eq_one_div]
      _ = M * q / (1 - q) := by ring
  calc
    ‖(tsum fun n : ℕ => h (k * n) * r ^ n) - h 0‖ = ‖∑' n : ℕ, f (n + 1)‖ := by
      rw [show (tsum fun n : ℕ => h (k * n) * r ^ n) = ∑' n : ℕ, f n by rfl, ← htail_eq]
    _ ≤ ∑' n : ℕ, M * q ^ (n + 1) := htail_le
    _ = M * q / (1 - q) := hmajorant_tsum
    _ = M * (1 / R) ^ k / (1 - (1 / R) ^ k) := by simp [q]

end

end Omega.Zeta
