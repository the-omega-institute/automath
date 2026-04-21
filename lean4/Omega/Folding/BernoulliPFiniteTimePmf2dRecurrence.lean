import Mathlib.Tactic

namespace Omega.Folding

/-- The audited two-variable denominator `D_p(u,z)` for the finite-time Bernoulli-`p` PMF
generating function. -/
def bernoulliPFiniteTimePmf2dDenominator (p u z : ℚ) : ℚ :=
  1 - ((1 - p) + p * u) * z

/-- The audited numerator `N_p(u,z)` is constant for the Bernoulli binomial walk. -/
def bernoulliPFiniteTimePmf2dNumerator (_p _u _z : ℚ) : ℚ :=
  1

/-- The bivariate rational generating function `F(u,z) = N_p(u,z) / D_p(u,z)`. -/
def bernoulliPFiniteTimePmf2dGeneratingFunction (p u z : ℚ) : ℚ :=
  bernoulliPFiniteTimePmf2dNumerator p u z / bernoulliPFiniteTimePmf2dDenominator p u z

/-- The exact finite-time PMF, defined by the coefficient recurrence extracted from the rational
generating function. -/
def bernoulliPFiniteTimePmf2d (p : ℚ) : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, 0 => (1 - p) * bernoulliPFiniteTimePmf2d p m 0
  | m + 1, k + 1 =>
      (1 - p) * bernoulliPFiniteTimePmf2d p m (k + 1) + p * bernoulliPFiniteTimePmf2d p m k

set_option maxHeartbeats 400000 in
/-- Comparing coefficients in the rational identity `D_p(u,z) F(u,z) = N_p(u,z)` yields the
two-dimensional Bernoulli-`p` PMF recurrence together with the explicit small-time seeds.
    thm:fold-bernoulli-p-finite-time-pmf-2d-recurrence -/
theorem paper_fold_bernoulli_p_finite_time_pmf_2d_recurrence
    (p u z : ℚ) :
    bernoulliPFiniteTimePmf2dGeneratingFunction p u z =
      1 / (1 - ((1 - p) + p * u) * z) ∧
      bernoulliPFiniteTimePmf2d p 0 0 = 1 ∧
      bernoulliPFiniteTimePmf2d p 0 1 = 0 ∧
      bernoulliPFiniteTimePmf2d p 1 0 = 1 - p ∧
      bernoulliPFiniteTimePmf2d p 1 1 = p ∧
      (∀ m, bernoulliPFiniteTimePmf2d p (m + 1) 0 = (1 - p) * bernoulliPFiniteTimePmf2d p m 0) ∧
      (∀ m k,
        bernoulliPFiniteTimePmf2d p (m + 1) (k + 1) =
          (1 - p) * bernoulliPFiniteTimePmf2d p m (k + 1) +
            p * bernoulliPFiniteTimePmf2d p m k) := by
  refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [bernoulliPFiniteTimePmf2dGeneratingFunction, bernoulliPFiniteTimePmf2dNumerator,
      bernoulliPFiniteTimePmf2dDenominator]
  · simp [bernoulliPFiniteTimePmf2d]
  · simp [bernoulliPFiniteTimePmf2d]
  · intro m
    rfl
  · intro m k
    rfl

end Omega.Folding
