import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-foldbin-s3-minimal-linear-complexity-three`. -/
theorem paper_conclusion_foldbin_s3_minimal_linear_complexity_three
    (S : ℕ → ℚ) (h2 : S 2 = 10) (h3 : S 3 = 26) (h4 : S 4 = 88)
    (hrec : ∀ m, 5 ≤ m →
      S m = 2 * S (m - 1) + 4 * S (m - 2) - 2 * S (m - 3)) :
    (S 5 = 260 ∧ S 6 = 820) ∧
      ¬ ∃ a b : ℚ, ∀ m, 4 ≤ m → S m = a * S (m - 1) + b * S (m - 2) := by
  have h5 : S 5 = 260 := by
    have h := hrec 5 (by norm_num)
    norm_num [h2, h3, h4] at h
    exact h
  have h6 : S 6 = 820 := by
    have h := hrec 6 (by norm_num)
    norm_num [h3, h4, h5] at h
    exact h
  refine ⟨⟨h5, h6⟩, ?_⟩
  rintro ⟨a, b, hlin⟩
  have hlin4 : (88 : ℚ) = a * 26 + b * 10 := by
    have h := hlin 4 (by norm_num)
    norm_num [h2, h3, h4] at h
    exact h
  have hlin5 : (260 : ℚ) = a * 88 + b * 26 := by
    have h := hlin 5 (by norm_num)
    norm_num [h2, h3, h4, h5] at h
    exact h
  have hlin6 : (820 : ℚ) = a * 260 + b * 88 := by
    have h := hlin 6 (by norm_num)
    norm_num [h2, h3, h4, h5, h6] at h
    exact h
  nlinarith [hlin4, hlin5, hlin6]

end Omega.Conclusion
