import Mathlib

namespace Omega.Zeta

open Filter

/-- Synthetic normalized ratios with exponentially summable adjacent-interaction tail. -/
noncomputable def xi_prime_hardcore_normalization_constant_ratio (t : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-(t ^ 2 * (1 - (1 / 2 : ℝ) ^ N)))

/-- Limiting normalization constant. -/
noncomputable def xi_prime_hardcore_normalization_constant_delta (t : ℝ) : ℝ :=
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
          (nhds (xi_prime_hardcore_normalization_constant_delta t)) ∧
        0 < xi_prime_hardcore_normalization_constant_delta t ∧
        ∀ N,
          0 ≤ xi_prime_hardcore_normalization_constant_ratio t N -
              xi_prime_hardcore_normalization_constant_delta t ∧
            xi_prime_hardcore_normalization_constant_ratio t N -
                xi_prime_hardcore_normalization_constant_delta t ≤
              t ^ 2 * (1 / 2 : ℝ) ^ N := by
  intro t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine strictAnti_nat_of_succ_lt ?_
    intro N
    have hpos : 0 <
        xi_prime_hardcore_normalization_constant_ratio t N := by
      unfold xi_prime_hardcore_normalization_constant_ratio
      exact Real.exp_pos _
    have htail_pos : 0 < t ^ 2 * (1 / 2 : ℝ) ^ (N + 1) := by
      have ht2 : 0 < t ^ 2 := by positivity
      positivity
    have hfactor_lt_one : Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ (N + 1))) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr htail_pos
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
        Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have harg :
        Tendsto (fun N : ℕ => -(t ^ 2 * (1 - (1 / 2 : ℝ) ^ N))) atTop
          (nhds (-t ^ 2)) := by
      have hone_minus :
          Tendsto (fun N : ℕ => 1 - (1 / 2 : ℝ) ^ N) atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hpow
      simpa using ((tendsto_const_nhds.mul hone_minus).neg)
    exact Real.continuous_exp.continuousAt.tendsto.comp harg
  · unfold xi_prime_hardcore_normalization_constant_delta
    exact Real.exp_pos _
  · intro N
    have hpow_nonneg : 0 ≤ (1 / 2 : ℝ) ^ N := by positivity
    have hpow_le_one : (1 / 2 : ℝ) ^ N ≤ 1 := by
      exact pow_le_one₀ (by positivity : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hratio_le_one :
        xi_prime_hardcore_normalization_constant_ratio t N ≤ 1 := by
      unfold xi_prime_hardcore_normalization_constant_ratio
      rw [Real.exp_le_one_iff]
      have hnonneg : 0 ≤ t ^ 2 * (1 - (1 / 2 : ℝ) ^ N) := by
        have ht2_nonneg : 0 ≤ t ^ 2 := by positivity
        nlinarith
      exact neg_nonpos.mpr hnonneg
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
      have hexp_le_one : Real.exp (-(t ^ 2 * (1 / 2 : ℝ) ^ N)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr htail_nonneg
      linarith
    refine ⟨?_, ?_⟩
    · rw [hsplit]
      have hratio_nonneg : 0 ≤ xi_prime_hardcore_normalization_constant_ratio t N := by
        unfold xi_prime_hardcore_normalization_constant_ratio
        positivity
      exact mul_nonneg hratio_nonneg hone_sub_nonneg
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
