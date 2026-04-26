import Mathlib.Tactic

open Filter

namespace Omega.POM

/-- Paper label: `cor:pom-curvature-uniform-limit-closed`. -/
theorem paper_pom_curvature_uniform_limit_closed :
    (let eps := fun m : ℕ =>
      (1 : ℝ) / 3 -
        (if Even (m + 1) then (1 : ℝ) else 2) / (3 * (2 : ℝ) ^ (m + 1));
      (∀ m : ℕ, 1 ≤ m →
        eps m =
          (1 : ℝ) / 3 -
            (if Even (m + 1) then (1 : ℝ) else 2) / (3 * (2 : ℝ) ^ (m + 1))) ∧
        Filter.Tendsto eps Filter.atTop (nhds ((1 : ℝ) / 3))) := by
  dsimp
  constructor
  · intro m _hm
    rfl
  · have hpow :
        Filter.Tendsto (fun m : ℕ => (2 : ℝ) ^ (m + 1)) Filter.atTop Filter.atTop := by
      have hpow_base : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop := by
        exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      exact hpow_base.comp (tendsto_add_atTop_nat 1)
    have hinv :
        Filter.Tendsto (fun m : ℕ => ((2 : ℝ) ^ (m + 1))⁻¹) Filter.atTop
          (nhds (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp hpow
    have htail :
        Filter.Tendsto
          (fun m : ℕ =>
            (if Even (m + 1) then (1 : ℝ) else 2) / (3 * (2 : ℝ) ^ (m + 1)))
          Filter.atTop (nhds (0 : ℝ)) := by
      have hbound :
          ∀ m : ℕ,
            (if Even (m + 1) then (1 : ℝ) else 2) /
                (3 * (2 : ℝ) ^ (m + 1)) ≤
              (2 / 3 : ℝ) * ((2 : ℝ) ^ (m + 1))⁻¹ := by
        intro m
        have hpow_pos : 0 < (2 : ℝ) ^ (m + 1) := by positivity
        by_cases hm : Even (m + 1)
        · simp [hm]
          field_simp [hpow_pos.ne']
          norm_num
        · simp [hm]
          field_simp [hpow_pos.ne']
          exact le_rfl
      have hnonneg :
          ∀ m : ℕ,
            0 ≤
              (if Even (m + 1) then (1 : ℝ) else 2) /
                (3 * (2 : ℝ) ^ (m + 1)) := by
        intro m
        have hden_pos : 0 < 3 * (2 : ℝ) ^ (m + 1) := by positivity
        have hnum_nonneg : 0 ≤ (if Even (m + 1) then (1 : ℝ) else 2) := by
          split <;> norm_num
        exact div_nonneg hnum_nonneg hden_pos.le
      have hlim :
          Filter.Tendsto (fun m : ℕ => (2 / 3 : ℝ) * ((2 : ℝ) ^ (m + 1))⁻¹)
            Filter.atTop (nhds (0 : ℝ)) := by
        simpa using (tendsto_const_nhds.mul hinv)
      exact squeeze_zero hnonneg hbound hlim
    simpa using (tendsto_const_nhds.sub htail :
      Filter.Tendsto
        (fun m : ℕ =>
          (1 : ℝ) / 3 -
            (if Even (m + 1) then (1 : ℝ) else 2) /
              (3 * (2 : ℝ) ^ (m + 1)))
        Filter.atTop (nhds ((1 : ℝ) / 3 - 0)))

end Omega.POM
