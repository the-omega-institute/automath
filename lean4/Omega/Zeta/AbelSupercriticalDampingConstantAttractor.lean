import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete data for the supercritical-damping attractor bound after a `k`-step decimation. -/
structure AbelSupercriticalDampingConstantAttractorData where
  coeff : ℕ → ℂ
  k : ℕ
  C : ℝ
  q : ℝ
  hk : 0 < k
  hC : 0 ≤ C
  hq_nonneg : 0 ≤ q
  hq_lt_one : q < 1
  coeff_zero_bound : ‖coeff 0‖ ≤ C
  coeff_bound : ∀ n : ℕ, ‖coeff (k * (n + 1))‖ ≤ C * q ^ (n + 1)

/-- The decimated Abel series sampled every `k` coefficients. -/
def abel_supercritical_damping_constant_attractor_sampled_series
    (D : AbelSupercriticalDampingConstantAttractorData) (r : ℂ) : ℂ :=
  ∑' n : ℕ, D.coeff (D.k * n) * r ^ n

/-- Uniform closed-form tail bound on the closed unit disk. -/
def abel_supercritical_damping_constant_attractor_statement
    (D : AbelSupercriticalDampingConstantAttractorData) : Prop :=
  ∀ r : ℂ, ‖r‖ ≤ 1 →
    ‖abel_supercritical_damping_constant_attractor_sampled_series D r - D.coeff 0‖ ≤
      D.C * D.q / (1 - D.q)

/-- Paper label: `prop:abel-supercritical-damping-constant-attractor`. -/
theorem paper_abel_supercritical_damping_constant_attractor
    (D : AbelSupercriticalDampingConstantAttractorData) :
    abel_supercritical_damping_constant_attractor_statement D := by
  intro r hr
  let f : ℕ → ℂ := fun n => D.coeff (D.k * n) * r ^ n
  have hmajorant_summable : Summable (fun n : ℕ => D.C * D.q ^ (n + 1)) := by
    have hgeom : Summable (fun n : ℕ => D.q ^ n) :=
      summable_geometric_of_lt_one D.hq_nonneg D.hq_lt_one
    convert hgeom.mul_left (D.C * D.q) using 1
    ext n
    rw [pow_add]
    ring
  have htail_bound : ∀ n : ℕ, ‖f (n + 1)‖ ≤ D.C * D.q ^ (n + 1) := by
    intro n
    have hrpow_nonneg : 0 ≤ ‖r‖ ^ (n + 1) := pow_nonneg (norm_nonneg r) _
    have hrpow_le_one : ‖r‖ ^ (n + 1) ≤ 1 := pow_le_one₀ (norm_nonneg r) hr
    have hcoeff_nonneg : 0 ≤ D.C * D.q ^ (n + 1) := by
      exact mul_nonneg D.hC (pow_nonneg D.hq_nonneg _)
    calc
      ‖f (n + 1)‖ = ‖D.coeff (D.k * (n + 1)) * r ^ (n + 1)‖ := by simp [f]
      _ = ‖D.coeff (D.k * (n + 1))‖ * ‖r‖ ^ (n + 1) := by rw [norm_mul, Complex.norm_pow]
      _ ≤ (D.C * D.q ^ (n + 1)) * ‖r‖ ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_right (D.coeff_bound n) hrpow_nonneg
      _ ≤ (D.C * D.q ^ (n + 1)) * 1 := by
        exact mul_le_mul_of_nonneg_left hrpow_le_one hcoeff_nonneg
      _ = D.C * D.q ^ (n + 1) := by ring
  have htail_norm_summable : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_bound hmajorant_summable
  have hf_bound : ∀ n : ℕ, ‖f n‖ ≤ D.C * D.q ^ n := by
    intro n
    cases n with
    | zero =>
        calc
          ‖f 0‖ = ‖D.coeff 0‖ := by simp [f]
          _ ≤ D.C := D.coeff_zero_bound
          _ = D.C * D.q ^ 0 := by simp
    | succ n =>
        simpa using htail_bound n
  have hmajorant : Summable (fun n : ℕ => D.C * D.q ^ n) :=
    (summable_geometric_of_lt_one D.hq_nonneg D.hq_lt_one).mul_left D.C
  have hnorm_summable : Summable (fun n : ℕ => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hf_bound hmajorant
  have hf_summable : Summable f := summable_norm_iff.mp hnorm_summable
  have htail_eq :
      (∑' n : ℕ, f (n + 1)) = (∑' n : ℕ, f n) - D.coeff 0 := by
    have hsplit : f 0 + ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
      simpa using hf_summable.sum_add_tsum_nat_add 1
    rw [eq_sub_iff_add_eq]
    simpa [f, add_comm, add_left_comm, add_assoc] using hsplit
  have htail_le :
      ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, D.C * D.q ^ (n + 1) := by
    calc
      ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm htail_norm_summable
      _ ≤ ∑' n : ℕ, D.C * D.q ^ (n + 1) :=
        Summable.tsum_le_tsum htail_bound htail_norm_summable hmajorant_summable
  have hmajorant_tsum : (∑' n : ℕ, D.C * D.q ^ (n + 1)) = D.C * D.q / (1 - D.q) := by
    calc
      (∑' n : ℕ, D.C * D.q ^ (n + 1)) = ∑' n : ℕ, (D.C * D.q) * D.q ^ n := by
        congr with n
        rw [pow_add]
        ring
      _ = (D.C * D.q) * ∑' n : ℕ, D.q ^ n := by rw [tsum_mul_left]
      _ = (D.C * D.q) * (1 / (1 - D.q)) := by
        rw [tsum_geometric_of_lt_one D.hq_nonneg D.hq_lt_one, inv_eq_one_div]
      _ = D.C * D.q / (1 - D.q) := by ring
  calc
    ‖abel_supercritical_damping_constant_attractor_sampled_series D r - D.coeff 0‖
        = ‖∑' n : ℕ, f (n + 1)‖ := by
          rw [show abel_supercritical_damping_constant_attractor_sampled_series D r = ∑' n : ℕ, f n by
              rfl, ← htail_eq]
    _ ≤ ∑' n : ℕ, D.C * D.q ^ (n + 1) := htail_le
    _ = D.C * D.q / (1 - D.q) := hmajorant_tsum

end

end Omega.Zeta
