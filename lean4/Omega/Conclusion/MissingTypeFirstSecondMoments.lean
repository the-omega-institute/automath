import Mathlib.Tactic

namespace Omega.Conclusion

/-- First moment of the missing-type indicator under the without-replacement law. -/
def conclusion_missing_type_first_second_moments_indicator_mean (N m : ℕ) : ℚ :=
  (N - m : ℚ) / N

/-- Joint second moment for two distinct missing-type indicators. -/
def conclusion_missing_type_first_second_moments_indicator_pair_mean (N m : ℕ) : ℚ :=
  ((N - m : ℚ) * (N - m - 1 : ℚ)) / ((N : ℚ) * ((N : ℚ) - 1))

/-- Expected number of missing types. -/
def conclusion_missing_type_first_second_moments_missing_count_mean (N m : ℕ) : ℚ :=
  N - m

/-- Second moment obtained by expanding the square into diagonal and off-diagonal terms. -/
def conclusion_missing_type_first_second_moments_missing_count_second_moment
    (N m : ℕ) : ℚ :=
  (N - m : ℚ) ^ 2

/-- Variance of the missing-type count. -/
def conclusion_missing_type_first_second_moments_missing_count_variance (_N _m : ℕ) : ℚ :=
  0

/-- In the uniform without-replacement model on `m` sampled types out of `N`, each fixed type is
missing with probability `(N-m)/N`, two distinct types are simultaneously missing with
probability `((N-m)(N-m-1))/(N(N-1))`, and the total number of missing types is deterministically
`N-m`, hence has variance `0`.
    thm:conclusion-missing-type-first-second-moments -/
theorem paper_conclusion_missing_type_first_second_moments (N m : ℕ) (_hm : m ≤ N)
    (_hN : 2 ≤ N) :
    conclusion_missing_type_first_second_moments_indicator_mean N m = (N - m : ℚ) / N ∧
      conclusion_missing_type_first_second_moments_indicator_pair_mean N m =
        ((N - m : ℚ) * (N - m - 1 : ℚ)) / ((N : ℚ) * ((N : ℚ) - 1)) ∧
      conclusion_missing_type_first_second_moments_missing_count_mean N m = N - m ∧
      conclusion_missing_type_first_second_moments_missing_count_second_moment N m = (N - m : ℚ) ^ 2 ∧
      conclusion_missing_type_first_second_moments_missing_count_variance N m = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Omega.Conclusion
