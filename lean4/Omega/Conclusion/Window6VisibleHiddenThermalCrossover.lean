import Mathlib.Tactic

theorem paper_conclusion_window6_visible_hidden_thermal_crossover :
    ∃! y : ℝ, 0 < y ∧ y < 1 ∧ 27 * y ^ 4 + 8 * y ^ 3 + 8 * y ^ 2 - 21 = 0 := by
  let f : ℝ → ℝ := fun y => 27 * y ^ 4 + 8 * y ^ 3 + 8 * y ^ 2 - 21
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    fun_prop
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    norm_num [f]
  obtain ⟨y, hyI, hfy⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hcont hzero_mem
  have hy_pos : 0 < y := by
    refine lt_of_le_of_ne hyI.1 ?_
    intro hy0
    subst y
    norm_num [f] at hfy
  have hy_lt_one : y < 1 := by
    refine lt_of_le_of_ne hyI.2 ?_
    intro hy1
    subst y
    norm_num [f] at hfy
  have hstrict :
      ∀ {a b : ℝ}, 0 < a → a < b → f a < f b := by
    intro a b ha hab
    have h2 : a ^ 2 < b ^ 2 :=
      pow_lt_pow_left₀ hab ha.le (by norm_num : (2 : ℕ) ≠ 0)
    have h3 : a ^ 3 < b ^ 3 :=
      pow_lt_pow_left₀ hab ha.le (by norm_num : (3 : ℕ) ≠ 0)
    have h4 : a ^ 4 < b ^ 4 :=
      pow_lt_pow_left₀ hab ha.le (by norm_num : (4 : ℕ) ≠ 0)
    nlinarith [h2, h3, h4]
  refine ⟨y, ⟨hy_pos, hy_lt_one, by simpa [f] using hfy⟩, ?_⟩
  intro z hz
  by_cases hzy : z = y
  · exact hzy
  rcases lt_or_gt_of_ne hzy with hlt | hgt
  · have hlt_values : f z < f y := hstrict hz.1 hlt
    have hz_root : f z = 0 := by simpa [f] using hz.2.2
    nlinarith
  · have hlt_values : f y < f z := hstrict hy_pos hgt
    have hz_root : f z = 0 := by simpa [f] using hz.2.2
    nlinarith
