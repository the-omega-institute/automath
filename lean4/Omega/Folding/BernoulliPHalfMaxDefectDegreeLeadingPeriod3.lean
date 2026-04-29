import Mathlib.Tactic

namespace Omega.Folding

/-- Concrete data extracted from the `p = 1/2` maximal-defect recurrence. The degree step models
the fact that only the `u^3 M_{m-3}` term reaches the top degree, while the leading coefficient is
recorded as a period-`3` sequence after the three base values `(1, 2, 2)`. -/
structure BernoulliPHalfMaxDefectDegreeData where
  maxDefectDegree : ℕ → ℕ
  extremeStateCount : ℕ → ℕ
  leadingCoeff : ℕ → ℤ
  degree_two : maxDefectDegree 2 = 1
  degree_step : ∀ m, 2 ≤ m → maxDefectDegree (m + 1) = maxDefectDegree m + 1
  extremeState_le_degree : ∀ m, extremeStateCount m ≤ maxDefectDegree m
  leadingCoeff_two : leadingCoeff 2 = 1
  leadingCoeff_three : leadingCoeff 3 = 2
  leadingCoeff_four : leadingCoeff 4 = 2
  leadingCoeff_period3 : ∀ m, 2 ≤ m → leadingCoeff (m + 3) = leadingCoeff m

/-- Degree/defect package: the maximal defect has degree `m - 1`, the extreme-state count is
bounded by the same quantity, and the top coefficient is the `3`-periodic pattern `(1, 2, 2)`. -/
def BernoulliPHalfMaxDefectDegreeStatement (h : BernoulliPHalfMaxDefectDegreeData) : Prop :=
  (∀ m, 2 ≤ m → h.maxDefectDegree m = m - 1) ∧
    (∀ m, 2 ≤ m → h.extremeStateCount m ≤ m - 1) ∧
    (∀ m, 2 ≤ m → h.leadingCoeff m = if m % 3 = 2 then 1 else 2)

/-- The maximal-defect degree grows by one at each step from `m = 2` onward, and the leading
coefficient repeats with period `3` from the base triple `(1, 2, 2)`.
    prop:fold-bernoulli-p-half-max-defect-degree-and-leading-period3 -/
theorem paper_fold_bernoulli_p_half_max_defect_degree_and_leading_period3
    (h : BernoulliPHalfMaxDefectDegreeData) : BernoulliPHalfMaxDefectDegreeStatement h := by
  dsimp [BernoulliPHalfMaxDefectDegreeStatement]
  have hdeg : ∀ m, 2 ≤ m → h.maxDefectDegree m = m - 1 := by
    intro m
    induction' m using Nat.strong_induction_on with m ih
    intro hm
    by_cases h2 : m = 2
    · simpa [h2] using h.degree_two
    have hm1_lt : m - 1 < m := by omega
    have hm1_ge : 2 ≤ m - 1 := by omega
    have hprev := ih (m - 1) hm1_lt hm1_ge
    have hstep := h.degree_step (m - 1) hm1_ge
    have hm_eq : (m - 1) + 1 = m := by omega
    calc
      h.maxDefectDegree m = h.maxDefectDegree (m - 1) + 1 := by simpa [hm_eq] using hstep
      _ = ((m - 1) - 1) + 1 := by rw [hprev]
      _ = m - 1 := by omega
  have hext : ∀ m, 2 ≤ m → h.extremeStateCount m ≤ m - 1 := by
    intro m hm
    simpa [hdeg m hm] using h.extremeState_le_degree m
  have hlead : ∀ m, 2 ≤ m → h.leadingCoeff m = if m % 3 = 2 then 1 else 2 := by
    intro m
    induction' m using Nat.strong_induction_on with m ih
    intro hm
    by_cases h2 : m = 2
    · subst h2
      norm_num [h.leadingCoeff_two]
    by_cases h3 : m = 3
    · subst h3
      norm_num [h.leadingCoeff_three]
    by_cases h4 : m = 4
    · subst h4
      norm_num [h.leadingCoeff_four]
    have hm3_lt : m - 3 < m := by omega
    have hm3_ge : 2 ≤ m - 3 := by omega
    have hprev := ih (m - 3) hm3_lt hm3_ge
    have hperiod := h.leadingCoeff_period3 (m - 3) hm3_ge
    have hm_eq : (m - 3) + 3 = m := by omega
    calc
      h.leadingCoeff m = h.leadingCoeff (m - 3) := by simpa [hm_eq] using hperiod
      _ = if (m - 3) % 3 = 2 then 1 else 2 := hprev
      _ = if m % 3 = 2 then 1 else 2 := by
        have hmod : (m - 3) % 3 = m % 3 := by omega
        rw [hmod]
  exact ⟨hdeg, hext, hlead⟩

end Omega.Folding
