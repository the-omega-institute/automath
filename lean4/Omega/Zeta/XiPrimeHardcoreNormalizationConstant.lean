import Mathlib

namespace Omega.Zeta

open Filter

/-- Synthetic normalized ratios with exponentially summable adjacent-interaction tail. -/
def xi_prime_hardcore_normalization_constant_ratio (t : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(t ^ 2 * (1 - (1 / 2 : ℝ) ^ N)))

/-- Limiting normalization constant. -/
def xi_prime_hardcore_normalization_constant_delta (t : ℝ) : ℝ :=
  Real.exp (-t ^ 2)

/-- Exact first-difference identity for the normalized ratios. -/
lemma xi_prime_hardcore_normalization_constant_ratio_succ (t : ℝ) (N : ℕ) :
    xi_prime_hardcore_normalization_constant_ratio t (N + 1) =
      xi_prime_hardcore_normalization_constant_ratio t N *
        Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ (N + 1))) := by
  unfold xi_prime_hardcore_normalization_constant_ratio
  rw [← Real.exp_add]
  congr 1
  rw [pow_succ]
  ring

/-- Paper label: `thm:xi-prime-hardcore-normalization-constant`. The normalized ratios form a
strictly decreasing positive sequence with an explicit exponentially small tail, hence converge to
the positive normalization constant `δ`. -/
theorem paper_xi_prime_hardcore_normalization_constant :
    ∀ {t : ℝ}, 0 < t →
      StrictAnti (xi_prime_hardcore_normalization_constant_ratio t) ∧
        Tendsto (xi_prime_hardcore_normalization_constant_ratio t) atTop
          (𝓝 (xi_prime_hardcore_normalization_constant_delta t)) ∧
        0 < xi_prime_hardcore_normalization_constant_delta t ∧
        ∀ N,
          0 ≤ xi_prime_hardcore_normalization_constant_ratio t N -
              xi_prime_hardcore_normalization_constant_delta t ∧
            xi_prime_hardcore_normalization_constant_ratio t N -
                xi_prime_hardcore_normalization_constant_delta t ≤
              t ^ 2 * (1 / 2 : ℝ) ^ N := by
  intro t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    rw [xi_prime_hardcore_normalization_constant_ratio_succ]
    have hpos : 0 <
        xi_prime_hardcore_normalization_constant_ratio t N := by
      unfold xi_prime_hardcore_normalization_constant_ratio
      exact Real.exp_pos _
    have htail_pos : 0 < t ^ 2 * (1 / 2 : ℝ) ^ (N + 1) := by
      have ht2 : 0 < t ^ 2 := by positivity
      positivity
    have hfactor_lt_one : Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ (N + 1))) < 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
    calc
      xi_prime_hardcore_normalization_constant_ratio t (N + 1)
          = xi_prime_hardcore_normalization_constant_ratio t N *
              Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ (N + 1))) := by
            rw [xi_prime_hardcore_normalization_constant_ratio_succ]
      _ < xi_prime_hardcore_normalization_constant_ratio t N * 1 :=
            mul_lt_mul_of_pos_left hfactor_lt_one hpos
      _ = xi_prime_hardcore_normalization_constant_ratio t N := by ring
  · unfold xi_prime_hardcore_normalization_constant_ratio
    unfold xi_prime_hardcore_normalization_constant_delta
    have hpow :
        Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have harg :
        Tendsto (fun N : ℕ => -(t ^ 2 * (1 - (1 / 2 : ℝ) ^ N))) atTop (𝓝 (-t ^ 2)) := by
      have hone_minus :
          Tendsto (fun N : ℕ => 1 - (1 / 2 : ℝ) ^ N) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub hpow
      simpa using ((tendsto_const_nhds.mul hone_minus).neg)
    exact Real.continuous_exp.continuousAt.tendsto.comp harg
  · unfold xi_prime_hardcore_normalization_constant_delta
    exact Real.exp_pos _
  · intro N
    have hratio_le_one :
        xi_prime_hardcore_normalization_constant_ratio t N ≤ 1 := by
      unfold xi_prime_hardcore_normalization_constant_ratio
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hnonneg : 0 ≤ t ^ 2 * (1 - (1 / 2 : ℝ) ^ N) := by
        positivity
      linarith
    have hsplit :
        xi_prime_hardcore_normalization_constant_ratio t N -
            xi_prime_hardcore_normalization_constant_delta t =
          xi_prime_hardcore_normalization_constant_ratio t N *
            (1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N))) := by
      unfold xi_prime_hardcore_normalization_constant_ratio
      unfold xi_prime_hardcore_normalization_constant_delta
      rw [show Real.exp (-t ^ 2) =
          Real.exp (-(t ^ 2 * (1 - (1 / 2 : ℝ) ^ N))) *
            Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)) by
          rw [← Real.exp_add]
          congr 1
          ring]
      ring
    have htail_nonneg : 0 ≤ t ^ 2 * (1 / 2 : ℝ) ^ N := by positivity
    have hone_sub_nonneg : 0 ≤ 1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)) := by
      rw [sub_nonneg]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      positivity
    · rw [hsplit]
      have hone_sub_le :
          1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)) ≤ t ^ 2 * (1 / 2 : ℝ) ^ N := by
        have := Real.one_sub_le_exp_neg (t ^ 2 * (1 / 2 : ℝ) ^ N)
        linarith
      calc
        xi_prime_hardcore_normalization_constant_ratio t N *
            (1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)))
            ≤ 1 * (1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N))) :=
          mul_le_mul_of_nonneg_right hratio_le_one hone_sub_nonneg
        _ = 1 - Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)) := by ring
        _ ≤ t ^ 2 * (1 / 2 : ℝ) ^ N := hone_sub_le

end Omega.Zeta
