import Mathlib

namespace Omega.Conclusion

/-- Some phase grid point of the form `arccos (1 - 2k/d)` lands in every open subinterval of
`[0, π]`.
`thm:conclusion-hypercube-phase-grid-dense` -/
theorem paper_conclusion_hypercube_phase_grid_dense (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ Real.pi)
    (hab : a < b) :
    ∃ d k : ℕ,
      1 ≤ d ∧
        k ≤ d ∧
          a < Real.arccos (1 - 2 * (k : ℝ) / d) ∧
            Real.arccos (1 - 2 * (k : ℝ) / d) < b := by
  let x₀ : ℝ := (1 - Real.cos a) / 2
  let x₁ : ℝ := (1 - Real.cos b) / 2
  have hcos : Real.cos b < Real.cos a := Real.cos_lt_cos_of_nonneg_of_le_pi ha hb hab
  have hx : x₀ < x₁ := by
    dsimp [x₀, x₁]
    linarith
  obtain ⟨q, hqx₀, hqx₁⟩ := exists_rat_btwn hx
  have hx₀_nonneg : 0 ≤ x₀ := by
    dsimp [x₀]
    linarith [Real.cos_le_one a]
  have hx₁_le_one : x₁ ≤ 1 := by
    dsimp [x₁]
    linarith [Real.neg_one_le_cos b]
  have hq_pos : 0 < (q : ℝ) := lt_of_le_of_lt hx₀_nonneg hqx₀
  have hq_lt_one : (q : ℝ) < 1 := hqx₁.trans_le hx₁_le_one
  have hq_pos_rat : (0 : ℚ) < q := by
    exact_mod_cast hq_pos
  let d : ℕ := q.den
  let k : ℕ := Int.toNat q.num
  have hd_pos : 0 < d := by
    simpa [d] using q.den_pos
  have hq_num_pos : 0 < q.num := Rat.num_pos.mpr hq_pos_rat
  have hk_int : (k : ℤ) = q.num := by
    simpa [k] using Int.toNat_of_nonneg hq_num_pos.le
  have hq_eq : (q : ℝ) = (k : ℝ) / d := by
    calc
      (q : ℝ) = (q.num : ℝ) / q.den := by
        exact_mod_cast (Rat.num_div_den q).symm
      _ = (k : ℝ) / d := by
        rw [show (q.num : ℝ) = (k : ℝ) by
              have hk_real : (k : ℝ) = q.num := by
                exact_mod_cast hk_int
              simpa using hk_real.symm]
  have hk_lt_d_real : (k : ℝ) < d := by
    have hd_pos_real : (0 : ℝ) < d := by
      exact_mod_cast hd_pos
    have hdiv_lt_one : (k : ℝ) / d < 1 := by
      rw [← hq_eq]
      exact hq_lt_one
    have : (k : ℝ) < 1 * d := (div_lt_iff₀ hd_pos_real).mp hdiv_lt_one
    simpa using this
  have hk_le_d : k ≤ d := by
    exact Nat.le_of_lt (by exact_mod_cast hk_lt_d_real)
  have hb_nonneg : 0 ≤ b := le_trans ha (le_of_lt hab)
  have ht_eq : 1 - 2 * (k : ℝ) / d = 1 - 2 * (q : ℝ) := by
    rw [hq_eq]
    ring
  have ht_lower : -1 ≤ 1 - 2 * (k : ℝ) / d := by
    rw [ht_eq]
    linarith
  have ht_upper : 1 - 2 * (k : ℝ) / d ≤ 1 := by
    rw [ht_eq]
    linarith
  have ht_lt_cos_a : 1 - 2 * (k : ℝ) / d < Real.cos a := by
    rw [ht_eq] at *
    dsimp [x₀] at hqx₀
    linarith
  have hcos_b_lt_t : Real.cos b < 1 - 2 * (k : ℝ) / d := by
    rw [ht_eq] at *
    dsimp [x₁] at hqx₁
    linarith
  refine ⟨d, k, Nat.succ_le_of_lt hd_pos, hk_le_d, ?_, ?_⟩
  · have :=
      Real.arccos_lt_arccos ht_lower ht_lt_cos_a (Real.cos_le_one a)
    simpa [Real.arccos_cos ha (le_trans (le_of_lt hab) hb)] using this
  · have :=
      Real.arccos_lt_arccos (Real.neg_one_le_cos b) hcos_b_lt_t ht_upper
    simpa [Real.arccos_cos hb_nonneg hb] using this

end Omega.Conclusion
