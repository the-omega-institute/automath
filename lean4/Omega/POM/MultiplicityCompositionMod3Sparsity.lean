import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.POM

/-- Weighted composition count for compositions of `L` using parts `1` and `2`, with a factor
`u` attached to every part equal to `1`. -/
noncomputable def mod3SparseWeightedCount (u : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => u
  | n + 2 => u * mod3SparseWeightedCount u (n + 1) + mod3SparseWeightedCount u n

/-- Count of compositions of `L` into parts `1` and `2` having at most one part congruent to
`1 mod 3`. In this simplified model the only bad residue class is the part `1` itself. -/
def mod3SparseEventCount : ℕ → ℕ
  | 0 => 1
  | n + 1 => if (n + 1) % 2 = 0 then 1 else (n + 2) / 2

/-- Dominant scale for the `u = 1/2` transfer recurrence. -/
noncomputable def mod3SparseHalfScale : ℝ :=
  (1 + Real.sqrt 17) / 4

/-- Associated exponential ratio after comparing against the `2^(L/2)` lower bound coming from
the Fibonacci denominator. -/
noncomputable def mod3SparseEta : ℝ :=
  mod3SparseHalfScale / Real.sqrt 2

private theorem weightedCount_one_eq_fib : ∀ n : ℕ,
    mod3SparseWeightedCount 1 n = Nat.fib (n + 1)
  | 0 => by simp [mod3SparseWeightedCount]
  | 1 => by simp [mod3SparseWeightedCount]
  | n + 2 => by
      simp [mod3SparseWeightedCount, weightedCount_one_eq_fib (n + 1), weightedCount_one_eq_fib n,
        Omega.fib_succ_succ']

private theorem mod3SparseHalfScale_sq :
    mod3SparseHalfScale ^ 2 = mod3SparseHalfScale / 2 + 1 := by
  unfold mod3SparseHalfScale
  have hsqrt : (Real.sqrt 17 : ℝ) ^ 2 = 17 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by positivity)]
  nlinarith

private theorem weightedCount_half_le_scale_pow : ∀ n : ℕ,
    mod3SparseWeightedCount (1 / 2) n ≤ mod3SparseHalfScale ^ n
  | 0 => by
      simp [mod3SparseWeightedCount, mod3SparseHalfScale]
  | 1 => by
      simp [mod3SparseWeightedCount, mod3SparseHalfScale]
      have hsqrt_gt_one : (1 : ℝ) < Real.sqrt 17 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt 17 := by positivity
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by positivity)]
      nlinarith
  | n + 2 => by
      calc
        mod3SparseWeightedCount (1 / 2) (n + 2)
            = (1 / 2) * mod3SparseWeightedCount (1 / 2) (n + 1) +
                mod3SparseWeightedCount (1 / 2) n := by
                  simp [mod3SparseWeightedCount]
        _ ≤ (1 / 2) * mod3SparseHalfScale ^ (n + 1) + mod3SparseHalfScale ^ n := by
              gcongr
              exact weightedCount_half_le_scale_pow (n + 1)
              exact weightedCount_half_le_scale_pow n
        _ = mod3SparseHalfScale ^ n * (1 + mod3SparseHalfScale / 2) := by
              ring
        _ = mod3SparseHalfScale ^ n * mod3SparseHalfScale ^ 2 := by
              rw [mod3SparseHalfScale_sq]
              ring
        _ = mod3SparseHalfScale ^ (n + 2) := by
              rw [← pow_add]

private theorem fib_lower_by_sqrt_two (L : ℕ) :
    (Real.sqrt 2) ^ L / Real.sqrt 2 ≤ (Nat.fib (L + 1) : ℝ) := by
  rcases Nat.even_or_odd L with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hmain : (Real.sqrt 2) ^ (2 * k) / Real.sqrt 2 ≤ (Nat.fib (2 * k + 1) : ℝ) := by
      have hnat : 2 ^ k ≤ Nat.fib (2 * k + 1) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          Omega.fib_exponential_growth 1 k (by omega)
      have hreal : ((2 : ℝ) ^ k) ≤ (Nat.fib (2 * k + 1) : ℝ) := by
        exact_mod_cast hnat
      have hsqrt_pos : 0 < Real.sqrt 2 := by positivity
      have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := by positivity
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
      calc
        (Real.sqrt 2) ^ (2 * k) / Real.sqrt 2
            = (2 : ℝ) ^ k / Real.sqrt 2 := by
                rw [pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        _ ≤ (2 : ℝ) ^ k := by
              have hpow_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
              exact (div_le_iff₀ hsqrt_pos).2 <| by nlinarith
        _ ≤ (Nat.fib (2 * k + 1) : ℝ) := hreal
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hmain
  · have hmain : (Real.sqrt 2) ^ (2 * k + 1) / Real.sqrt 2 ≤ (Nat.fib (2 * k + 2) : ℝ) := by
      have hnat : 2 ^ k ≤ Nat.fib (2 * k + 2) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using
          Omega.fib_exponential_growth 2 k (by omega)
      have hreal : ((2 : ℝ) ^ k) ≤ (Nat.fib (2 * k + 2) : ℝ) := by
        exact_mod_cast hnat
      have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
      calc
        (Real.sqrt 2) ^ (2 * k + 1) / Real.sqrt 2 = (Real.sqrt 2) ^ (2 * k) := by
          field_simp [hsqrt_ne]
          ring
        _ = (2 : ℝ) ^ k := by
              rw [pow_mul, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
        _ ≤ (Nat.fib (2 * k + 2) : ℝ) := hreal
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hmain

private theorem mod3SparseHalfScale_lt_sqrt_two :
    mod3SparseHalfScale < Real.sqrt 2 := by
  have hlt_two : mod3SparseHalfScale < 2 := by
    unfold mod3SparseHalfScale
    have hsqrt17_lt_seven : Real.sqrt 17 < 7 := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt 17 := by positivity
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by positivity)]
    nlinarith
  have hsq_lt : mod3SparseHalfScale ^ 2 < 2 := by
    nlinarith [mod3SparseHalfScale_sq, hlt_two]
  have hnonneg : 0 ≤ mod3SparseHalfScale := by
    unfold mod3SparseHalfScale
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := by positivity
  have hsqrt_sq : (Real.sqrt 2 : ℝ) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  nlinarith

private theorem weighted_half_pair_lower :
    ∀ k : ℕ,
      1 ≤ mod3SparseWeightedCount (1 / 2) (2 * k) ∧
        ((k + 1 : ℝ) / 2) ≤ mod3SparseWeightedCount (1 / 2) (2 * k + 1)
  | 0 => by
      simp [mod3SparseWeightedCount]
  | k + 1 => by
      rcases weighted_half_pair_lower k with ⟨heven, hodd⟩
      have hodd_nonneg : 0 ≤ mod3SparseWeightedCount (1 / 2) (2 * k + 1) := by
        have : 0 ≤ ((k + 1 : ℝ) / 2) := by positivity
        linarith
      have heven_next : 1 ≤ mod3SparseWeightedCount (1 / 2) (2 * (k + 1)) := by
        calc
          1 ≤ (1 / 2) * mod3SparseWeightedCount (1 / 2) (2 * k + 1) +
                mod3SparseWeightedCount (1 / 2) (2 * k) := by
                linarith
          _ = mod3SparseWeightedCount (1 / 2) (2 * (k + 1)) := by
                simp [mod3SparseWeightedCount, two_mul, add_assoc, add_left_comm, add_comm]
      have hodd_next :
          (((k + 1 : ℝ) + 1) / 2) ≤ mod3SparseWeightedCount (1 / 2) (2 * (k + 1) + 1) := by
        calc
          ((k + 1 : ℝ) + 1) / 2 = (1 / 2 : ℝ) + (k + 1 : ℝ) / 2 := by ring
          _ ≤ (1 / 2) * mod3SparseWeightedCount (1 / 2) (2 * (k + 1)) +
                mod3SparseWeightedCount (1 / 2) (2 * k + 1) := by
                  linarith
          _ = mod3SparseWeightedCount (1 / 2) (2 * (k + 1) + 1) := by
                simp [mod3SparseWeightedCount, two_mul, add_assoc, add_left_comm, add_comm]
      exact ⟨heven_next, by simpa using hodd_next⟩

private theorem mod3SparseEventCount_even (k : ℕ) :
    mod3SparseEventCount (2 * k) = 1 := by
  cases k with
  | zero =>
      simp [mod3SparseEventCount]
  | succ k =>
      have hmod : (2 * k + 2) % 2 = 0 := by omega
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring]
      simp [mod3SparseEventCount, hmod]

private theorem mod3SparseEventCount_odd (k : ℕ) :
    mod3SparseEventCount (2 * k + 1) = k + 1 := by
  have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
  rw [mod3SparseEventCount, if_neg hmod]
  omega

private theorem mod3SparseEventCount_le_two_weighted (L : ℕ) :
    (mod3SparseEventCount L : ℝ) ≤ 2 * mod3SparseWeightedCount (1 / 2) L := by
  rcases Nat.even_or_odd L with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rcases weighted_half_pair_lower k with ⟨heven, -⟩
    have hcount : mod3SparseEventCount (k + k) = 1 := by
      simpa [two_mul] using mod3SparseEventCount_even k
    have heven' : 1 ≤ mod3SparseWeightedCount (1 / 2) (k + k) := by
      simpa [two_mul] using heven
    rw [hcount]
    have htarget : (1 : ℝ) ≤ 2 * mod3SparseWeightedCount (1 / 2) (k + k) := by
      nlinarith [heven']
    simpa using htarget
  · rcases weighted_half_pair_lower k with ⟨-, hodd⟩
    have hcount : mod3SparseEventCount (2 * k + 1) = k + 1 := mod3SparseEventCount_odd k
    rw [hcount]
    have htarget : (k + 1 : ℝ) ≤ 2 * mod3SparseWeightedCount (1 / 2) (2 * k + 1) := by
      nlinarith [hodd]
    simpa using htarget

/-- A concrete exponential sparsity proxy for ordered compositions into parts `1` and `2`.
The proof keeps the weighted generating-function comparison at `u = 1/2`, identifies the
dominant scale `(1 + √17) / 4`, and compares it to the Fibonacci growth at `u = 1`.
    thm:pom-multiplicity-composition-mod3-sparsity -/
theorem paper_pom_multiplicity_composition_mod3_sparsity :
    0 < mod3SparseEta ∧ mod3SparseEta < 1 ∧
      ∀ L : ℕ,
        (2 * mod3SparseWeightedCount (1 / 2) L) / (Nat.fib (L + 1) : ℝ) ≤
          (2 * Real.sqrt 2) * mod3SparseEta ^ L := by
  have heta_pos : 0 < mod3SparseEta := by
    unfold mod3SparseEta
    have hscale_pos : 0 < mod3SparseHalfScale := by
      unfold mod3SparseHalfScale
      have hsqrt_pos : 0 < Real.sqrt 17 := by positivity
      nlinarith
    have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
    exact div_pos hscale_pos hsqrt2_pos
  refine ⟨heta_pos, ?_, ?_⟩
  · unfold mod3SparseEta
    have hsqrt2_pos : 0 < Real.sqrt 2 := by positivity
    exact (div_lt_one hsqrt2_pos).2 mod3SparseHalfScale_lt_sqrt_two
  · intro L
    have hFib_pos : 0 < (Nat.fib (L + 1) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    have hweighted :
        mod3SparseWeightedCount (1 / 2) L ≤ mod3SparseHalfScale ^ L :=
      weightedCount_half_le_scale_pow L
    have hnum_nonneg : 0 ≤ 2 * mod3SparseHalfScale ^ L := by
      have hscale_nonneg : 0 ≤ mod3SparseHalfScale := by
        unfold mod3SparseHalfScale
        positivity
      positivity
    have hsqrt_den_pos : 0 < (Real.sqrt 2) ^ L / Real.sqrt 2 := by positivity
    calc
      (2 * mod3SparseWeightedCount (1 / 2) L) / (Nat.fib (L + 1) : ℝ)
          ≤ (2 * mod3SparseHalfScale ^ L) / (Nat.fib (L + 1) : ℝ) := by
              exact div_le_div_of_nonneg_right (by gcongr) hFib_pos.le
      _ ≤ (2 * mod3SparseHalfScale ^ L) / ((Real.sqrt 2) ^ L / Real.sqrt 2) := by
            rw [div_le_div_iff₀ hFib_pos hsqrt_den_pos]
            nlinarith [fib_lower_by_sqrt_two L, hnum_nonneg]
      _ = (2 * Real.sqrt 2) * mod3SparseEta ^ L := by
            unfold mod3SparseEta
            have hsqrt2_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
            have hpow_ne : (Real.sqrt 2 : ℝ) ^ L ≠ 0 := by positivity
            rw [div_pow]
            field_simp [hsqrt2_ne, hpow_ne]

/-- The explicit event-count model is exponentially sparse relative to the Fibonacci
normalization, with the same decay ratio as the weighted `u = 1/2` proxy. -/
theorem paper_pom_multiplicity_composition_witten_sign_exp_sparse :
    ∃ C η : ℝ, 0 < η ∧ η < 1 ∧
      ∀ L : ℕ, (mod3SparseEventCount L : ℝ) / (Nat.fib (L + 1) : ℝ) ≤ C * η ^ L := by
  rcases paper_pom_multiplicity_composition_mod3_sparsity with ⟨heta_pos, heta_lt_one, hbound⟩
  refine ⟨2 * Real.sqrt 2, mod3SparseEta, heta_pos, heta_lt_one, ?_⟩
  intro L
  have hFib_nonneg : 0 ≤ (Nat.fib (L + 1) : ℝ) := by positivity
  calc
    (mod3SparseEventCount L : ℝ) / (Nat.fib (L + 1) : ℝ) ≤
        (2 * mod3SparseWeightedCount (1 / 2) L) / (Nat.fib (L + 1) : ℝ) := by
          exact div_le_div_of_nonneg_right (mod3SparseEventCount_le_two_weighted L) hFib_nonneg
    _ ≤ (2 * Real.sqrt 2) * mod3SparseEta ^ L := hbound L

end Omega.POM
