import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-bivariate-information-projection-halving`. -/
theorem paper_conclusion_poisson_bivariate_information_projection_halving (A B : ℝ) :
    (∀ α β : ℝ,
      A ^ 2 / 8 + B ^ 2 / 2 ≤
        A ^ 2 / 4 + B ^ 2 + α ^ 2 / 2 + β ^ 2 / 2 + B * α - A * β / 2) ∧
      (A ^ 2 / 4 + B ^ 2 + (-B) ^ 2 / 2 + (A / 2) ^ 2 / 2 + B * (-B) -
          A * (A / 2) / 2 =
        A ^ 2 / 8 + B ^ 2 / 2) ∧
        ((1 / 2 : ℝ) * (A ^ 2 / 8 + B ^ 2 / 2) = A ^ 2 / 16 + B ^ 2 / 4) := by
  constructor
  · intro α β
    nlinarith [sq_nonneg (α + B), sq_nonneg (β - A / 2)]
  · constructor <;> ring

end Omega.Conclusion
